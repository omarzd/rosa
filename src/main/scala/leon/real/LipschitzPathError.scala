/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import purescala.Common.Identifier
import purescala.TreeOps.{preMap, replace}

import real.TreeOps._
import real.Trees.{PlusR, WithInEq, MinusR, RealLiteral}
import Rational._
import Precision._


class LipschitzPathError(reporter: Reporter, solver: RangeSolver, precision: Precision,
  variables: VariablePool, silent: Boolean = false) {

  implicit val debugSection = utils.DebugSectionPathError

  val approximator = new AAApproximator(reporter, solver, precision, silent, checkPathError = true)
  val leonToZ3 = new LeonToZ3Transformer(variables, precision)

  /*val machineEps = precision match {
    case FPPrecision(bts) =>
      throw new Exception("Path error doesn't work yet with fixedpoints")
      zero
    case _ => getUnitRoundoff(precision)
  }*/
  
  /*
    @param rPath path taken by real values
    @param fPath alternative path, possibly taken by floats
  */
  // TODO: does not work for tuples
  def computePathError(precondition: Expr, rPath: Path, fPath: Path): Option[Rational] = {
    reporter.debug("precondition: " + precondition)
    reporter.debug("\n\n*****\nreal path: " + rPath.bodyReal + " -- " + rPath.condition)
    reporter.debug("fl path:   " + fPath.bodyReal + " -- " + fPath.condition)
    reporter.debug("initial vars: " + variables)

    val preAdditionalConstraints = {
      And(getClauses(precondition).filter(cl => !isRangeConstraint(cl)))
    }
    reporter.debug("preAdditionalConstraints: " + preAdditionalConstraints)

    val varsReal: Map[Expr, XReal] = approximator.approximateEquations(rPath.bodyFinite,
      precondition, variables, exactInputs = false)
    reporter.debug("varsReal: " + varsReal)

    val varsFloat = approximator.approximateEquations(fPath.bodyFinite, precondition,
      variables, exactInputs = false)
    reporter.debug("varsFloat: " + varsFloat)
    
    // interval for floats going the other way f2
    tightenInputs(precondition, rPath.condition, fPath.condition, varsReal) match {
      case None => reporter.debug("float infeasible")
        None

      case Some((rangeCnstr1, floatIntervals, otherConstraints1)) =>
        tightenInputs(precondition, fPath.condition, rPath.condition, varsFloat) match {
          case None => reporter.debug("real infeasible")
            None

          case Some((rangeCnstr2, rInts, otherConstraints2)) =>
            val criticalIntervals: Map[Expr, RationalInterval] = floatIntervals.map ({
              case (v @ Variable(_), r) => (v, r union rInts(v))
            })

            reporter.debug("critical intervals:    " + criticalIntervals)
            reporter.debug("float intervals: " + floatIntervals)
            reporter.debug("add cnstrs f1: " + otherConstraints1)
            reporter.debug("add cnstrs f2: " + otherConstraints2)

            reporter.debug("computing the real difference")
            val diffError = computeDifference(rPath.bodyReal, fPath.bodyReal, floatIntervals,
              And(And(otherConstraints1, otherConstraints2), preAdditionalConstraints))
            if (!silent) reporter.info("diff error: " + diffError)
            

            val lipschitzError = getLipschitzError(rPath.bodyReal, criticalIntervals,
              And(otherConstraints1, preAdditionalConstraints))
            if (!silent) reporter.info("lipschitz error: " + lipschitzError)

            
            val roundoffError = computeRoundoffError(fPath.bodyFinite, floatIntervals,
              And(otherConstraints1, preAdditionalConstraints))
            if (!silent) reporter.info("roundoff error: " + roundoffError)

            val totalError = lipschitzError + diffError + roundoffError
            if (!silent) reporter.info("total error: " + totalError)
            Some(totalError)
        }
    }
  }

  private def intervalsToConstraint(ints: Map[Expr, RationalInterval]): Expr = {
    And(ints.map({
      case (v @ Variable(_), RationalInterval(lo, hi)) => WithInEq(v, lo, hi)
    }).toSeq)
  }

  def computeRoundoffError(f: Expr, inputs: Map[Expr, RationalInterval],
    addConstraints: Expr): Rational = {
    val roundoffPre = And(intervalsToConstraint(inputs), addConstraints)
    approximator.computeErrorWithIntervals(f, roundoffPre, variables, inputs)
  }

  def computeDifference(f1: Expr, f2: Expr, inputs: Map[Expr, RationalInterval],
    addConstraints: Expr): Rational = {
    //println("computing difference: ")
    //println("f1: " + f1)
    //println("f2: " + f2)

    val z3Constraint = leonToZ3.getZ3Condition(And(intervalsToConstraint(inputs), addConstraints))
    //println("constraint: " + z3Constraint)
    

    // TODO Common subexpression elimination

    /*val (diff, tempVars) = (f1, f2) match {
      case (And(args1), And(args2)) =>

        val m1: Map[Expr, RationalInterval] = args1.foldLeft(Map[Expr, RationalInterval]())({
          case (currentMap, Equals(lhs, rhs)) =>
            currentMap +
            (lhs -> solver.getRange(z3Constraint, rhs, inputs, leonToZ3, solverMaxIterHigh, solverPrecisionHigh))
          case (currentMap, _) => currentMap
          })

        println("m1: " + m1)

        val m2: Map[Expr, RationalInterval] = args2.foldLeft(Map[Expr, RationalInterval]())({
          case (currentMap, Equals(lhs, rhs)) =>
            currentMap +
            (lhs -> solver.getRange(z3Constraint, rhs, inputs, leonToZ3, solverMaxIterHigh, solverPrecisionHigh))
          case (currentMap, _) => currentMap
          })

        println("m2: " + m2)


        (MinusR(args1.last, args2.last), m1 ++ m2)
      case _ => (null, null)
    }
    println("tempVars: " + tempVars)
    println("diff: " + diff)

    val tempVarsConstraint = leonToZ3.getZ3Condition(intervalsToConstraint(tempVars))
    println("tempVarsConstraint: " + tempVarsConstraint)


    */

    //val diff = MinusR(inlineBody(f1), inlineBody(f2))
    val diff = massageArithmetic( MinusR(inlineBody(f1), inlineBody(f2)) ) 
    
    val rangeDiff = solver.getRange(z3Constraint, diff, inputs, leonToZ3,
      solverMaxIterHigh, solverPrecisionHigh)
    max(abs(rangeDiff.xlo), abs(rangeDiff.xhi))
  }


  def getLipschitzError(f: Expr, ranges: Map[Expr, RationalInterval], addConstraints: Expr): Rational = {
    
    val ids = variables.inputs.keys.map(v => v.asInstanceOf[Variable].id).toSeq
    val derivs = ids.map( id => Calculus.d(inlineBody(f),id) )

    val z3Constraint = leonToZ3.getZ3Condition(And(intervalsToConstraint(ranges), addConstraints))

    val lipschitzConstants = derivs.map(der => {
      reporter.debug("computing range of derivative: " + der)
      val derMax = solver.getRange(z3Constraint, der, ranges, leonToZ3,
        solverMaxIterMedium, solverPrecisionMedium) 
      max(abs(derMax.xlo), abs(derMax.xhi))
      })

    val initErrorsMap = variables.getInitialErrors(precision)
    val initErrors = ids.map(id => initErrorsMap(id))
    // infinity norm:
    maxAbs(lipschitzConstants) * maxAbs(initErrors)
  }

  

  /*
   we currently only accept clauses of the form x < y where x, y can be constants or arithmetic expressions 
   @param precondition functions precondition
   @param c1 condition of real-valued path
   @param c2 condition of finite path
   @return (range constraint, tightened ranges, other constraints)
           returns None if the finite path is infeasible, given the constraints
  */
  def tightenInputs(precondition: Expr, c1: Expr, c2: Expr, vars: Map[Expr, XReal]):
    Option[(Expr, Map[Expr, RationalInterval], Expr)] = {
    def isSimpleComparison(e: Expr): Boolean = e match {
      case GreaterThan(_,_) | GreaterEquals(_,_) | LessThan(_,_) | LessEquals(_,_) => true
      case _ => false
    }
    
    // this can be done potentially more accurately, by taking the error of (rhs - lhs)
    def totalUncert(l: Expr, r: Expr): Rational = {
      val lhsUncert = approximator.computeErrorPreinitialized(idealToActual(l, variables),
        precondition, variables, vars)
 
      val rhsUncert = approximator.computeErrorPreinitialized(idealToActual(r, variables),
        precondition, variables, vars)
      rhsUncert + lhsUncert
    }

    def addErrors(e: Expr): Expr = e match {
      case GreaterThan(l, r) =>
        val totalErr = totalUncert(l, r)
        // This will introduce different deltas for the same error !!!
        val freshVar = VariableShop.getNewDelta        
        And(GreaterThan(l, PlusR(r, freshVar)), WithInEq(freshVar, -totalErr, totalErr))

      case GreaterEquals(l, r) =>
        val totalErr = totalUncert(l, r)
        // This will introduce different deltas for the same error !!!
        val freshVar = VariableShop.getNewDelta        
        And(GreaterEquals(l, PlusR(r, freshVar)), WithInEq(freshVar, -totalErr, totalErr))

      case LessThan(l, r) =>
        val totalErr = totalUncert(l, r)
        // This will introduce different deltas for the same error !!!
        val freshVar = VariableShop.getNewDelta        
        And(LessThan(l, PlusR(r, freshVar)), WithInEq(freshVar, -totalErr, totalErr))

      case LessEquals(l, r) =>
        val totalErr = totalUncert(l, r)
        // This will introduce different deltas for the same error !!!
        val freshVar = VariableShop.getNewDelta        
        And(LessEquals(l, PlusR(r, freshVar)), WithInEq(freshVar, -totalErr, totalErr))
    }

    reporter.debug("tightening inputs")

    val clauses = getClauses(c1)

    if (clauses.forall(cl => isSimpleComparison(cl))) {
      val (rangeClauses, otherClauses) = clauses.partition(cl => isRangeConstraint(cl))
      reporter.debug("all clauses: " + clauses)
      reporter.debug("rangeClauses: " + rangeClauses)
      reporter.debug("otherClauses: " + otherClauses)

      val otherConstraints = And(otherClauses.map(c => addErrors(c)))
      val rangeConstraint = And(rangeClauses.map(c => addErrors(c)))
      val z3Constraint = leonToZ3.getZ3Condition(And(And(rangeConstraint, c2),
        otherConstraints))

      val initialRanges =  variables.inputs.map({
        case (v, Record(i, lo, hi, Some(err), _, _)) =>
          (v, RationalInterval(lo - err, hi + err))
          // implicit roundoff
        case (v, Record(i, lo, hi, None, _, _)) =>
          val err = roundoff(lo, hi, precision)
          (v, RationalInterval(lo - err, hi + err))
      })
      reporter.debug("initialRanges: " + initialRanges)
      val z3InitialRanges = leonToZ3.getZ3Condition(intervalsToConstraint(initialRanges))

      val fullConstraint = And(z3Constraint, z3InitialRanges)

      // This would go even more accurate, if we did this altogether, 
      // essentially performing constraint propagation
      if (solver.isFeasible(fullConstraint, reporter)) {        
        val cMap: Map[Expr, RationalInterval] = initialRanges.map({
          case (v, r) =>
            val (interval, tmOut) = solver.tightenRange(v, fullConstraint, r,
              solverMaxIterHigh, solverPrecisionHigh)
            (v, interval)
        })

        Some(rangeConstraint, cMap, otherConstraints)
      } else {
        reporter.debug("apparently infeasible: " + z3Constraint) 
        None
      }
    } else {
      throw new Exception("Cannot handle this branch condition for path error computation: " + c1)
      null
    }
  }

  /*
    Computes the expression characterizing the values where can have diverging control flow,
    and also the intervals, if such computation is possible.
    Is going to throw an Exception if the condition is not in a fragment that we can handle,
    for instance, if it contains a disjunction.
  */
  /*def computeCriticalInterval(precondition: Expr, cond: Expr): (Expr, Map[Expr, RationalInterval]) = {
    def isSimpleComparison(e: Expr): Boolean = e match {
      case GreaterThan(_,_) | GreaterEquals(_,_) | LessThan(_,_) | LessEquals(_,_) => true
      case _ => false
    }

    def toEquality(e: Expr): Expr = e match {
      case GreaterThan(l, r) =>   Equals(l, r)
      case GreaterEquals(l, r) =>   Equals(l, r)
      case LessThan(l, r) =>      Equals(l, r)
      case LessEquals(l, r) =>    Equals(l, r)
    }

    def addErrors(e: Expr): Expr = e match {
      case Equals(lhs, rhs) =>
        val lhsUncert = approximator.computeError(idealToActual(lhs, variables), precondition, variables, false)
        val rhsUncert = approximator.computeError(idealToActual(rhs, variables), precondition, variables, false)
        val totalUncert = abs(rhsUncert - lhsUncert)

        val freshVar = VariableShop.getNewDelta
        And(Equals(lhs, PlusR(rhs, freshVar)), WithInEq(freshVar, -totalUncert, totalUncert))
    }

    val clauses = cond match {
      case And(args) => args
      case x => Seq(x)
    }

    if (clauses.forall(c => isSimpleComparison(c))) {
      val exactBranchpoints = clauses.map(c => toEquality(c))

      val withErrors = exactBranchpoints.map(c => addErrors(c))

      // I think we don't want the precondition here,
      // or maybe anything, but the range constraints
      val constraints = And(withErrors) //And(precondition, And(withErrors))
      println(constraints)
      val z3Constraint = leonToZ3.getZ3Condition(constraints)

      //computeInterval
      // This would go even more accurate, if we did this altogether, 
      // essentially performing constraint propagation
      val cMap: Map[Expr, RationalInterval] = variables.inputs.map({
        case (v @ Variable(_), Record(i, a, Some(lo), Some(hi), Some(err), None)) =>
          println("tightening: " + v)
          println(RationalInterval(lo - err, hi + err))

          val interval = solver.tightenRange(v, z3Constraint,
            RationalInterval(lo - err, hi + err), solverMaxIterHigh, solverPrecisionHigh)
          (v, interval)
      })

      (And(withErrors), cMap)
    } else {
      throw new Exception("Cannot handle this branch condition for path error computation: " + cond)
      null
    }
  }

  def computeFeasibleInterval(cExpr: Expr, cInts: Map[Expr, RationalInterval], fCond: Expr):
    Option[(Expr, Map[Expr, RationalInterval])] = {

    val constraint = And(cExpr, fCond)
    val z3Constraint = leonToZ3.getZ3Condition(constraint)

    if (solver.isFeasible(z3Constraint, reporter)) {

      val feasibilityMap: Map[Expr, RationalInterval] = cInts.map({
        case (v @ Variable(_), r @ RationalInterval(_,_)) =>
          (v, solver.tightenRange(v, z3Constraint, r, solverMaxIterHigh, solverPrecisionHigh))
        })
      Some(constraint, feasibilityMap)
    } else {
      None
    }
  }
  */
}