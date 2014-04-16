/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import purescala.Common.Identifier
import purescala.TreeOps.{preMap, replace}

import real.TreeOps.{idealToActual,inlineBody}
import real.Trees.{PlusR, WithInEq, MinusR}
import Rational._


class LipschitzPathError(reporter: Reporter, solver: RangeSolver, precision: Precision, variables: VariablePool) {

  val approximator = new AAApproximator(reporter, solver, precision, checkPathError = true)
  val leonToZ3 = new LeonToZ3Transformer(variables, precision)

  /*
    @param rPath path taken by real values
    @param fPath alternative path, possibly taken by floats
  */
  def computePathError(precondition: Expr, rPath: Path, fPath: Path): Seq[Rational] = {
    println("\n\n*****\nreal path: " + rPath.bodyReal + " -- " + rPath.condition)
    println("fl path:   " + fPath.bodyReal + " -- " + fPath.condition)
    println("initial vars: " + variables)
    
    // interval for floats going the other way f2
    tightenInputs(precondition, rPath.condition, fPath.condition) match {
      case None => println("float infeasible")
        Seq()

      case Some((cnstr, floatIntervals)) =>
        // Since the real values have to be "close"
        tightenInputs(precondition, fPath.condition, rPath.condition) match {
          case None => println("real infeasible")
            Seq()

          case Some((cnstr, rInts)) =>
            val criticalIntervals: Map[Expr, RationalInterval] = floatIntervals.map ({
              case (v @ Variable(_), r) => (v, r union rInts(v))
            })

            println("all:    " + criticalIntervals)
            println("floats: " + floatIntervals)

            
            val lipschitzError = getLipschitzError(rPath.bodyReal, criticalIntervals)
            println("lipschitz error: " + lipschitzError)

            val diffError = computeDifference(rPath.bodyReal, fPath.bodyReal, floatIntervals)
            println("diff error: " + diffError)
            
            val roundoffError = computeRoundoffError(fPath.bodyFinite, floatIntervals)
            println("roundoff error: " + roundoffError)

            val totalError = lipschitzError + diffError + roundoffError
            println("total error: " + totalError)
            Seq(totalError)
        }
    }
  }

  private def intervalsToConstraint(ints: Map[Expr, RationalInterval]): Expr = {
    And(ints.map({
      case (v @ Variable(_), RationalInterval(lo, hi)) => WithInEq(v, lo, hi)
    }).toSeq)
  }

  def computeRoundoffError(f: Expr, inputs: Map[Expr, RationalInterval]): Rational = {
    val roundoffPre = intervalsToConstraint(inputs)
    approximator.computeErrorWithIntervals(f, roundoffPre, variables, inputs)
  }

  def computeDifference(f1: Expr, f2: Expr, inputs: Map[Expr, RationalInterval]): Rational = {
    val diff = MinusR(inlineBody(f1), inlineBody(f2))
    val z3Constraint = leonToZ3.getZ3Condition(intervalsToConstraint(inputs))

    val rangeDiff = solver.getRange(z3Constraint, diff, inputs, leonToZ3,
      solverMaxIterHigh, solverPrecisionHigh)
    max(abs(rangeDiff.xlo), abs(rangeDiff.xhi))
  }


  def getLipschitzError(f: Expr, ranges: Map[Expr, RationalInterval]): Rational = {
    
    val ids = variables.inputs.keys.map(v => v.asInstanceOf[Variable].id).toSeq
    val derivs = ids.map( id => Calculus.d(inlineBody(f),id) )

    val z3Constraint = leonToZ3.getZ3Condition(intervalsToConstraint(ranges))

    val lipschitzConstants = derivs.map(der => {
      val derMax = solver.getRange(z3Constraint, der, ranges, leonToZ3,
        solverMaxIterMedium, solverPrecisionMedium) 
      max(abs(derMax.xlo), abs(derMax.xhi))
      })

    val initErrorsMap = variables.getInitialErrors(precision)
    val initErrors = ids.map(id => initErrorsMap(id))
    // infinity norm:
    maxAbs(lipschitzConstants) * maxAbs(initErrors)
  }

  def tightenInputs(precondition: Expr, c1: Expr, c2: Expr): Option[(Expr, Map[Expr, RationalInterval])] = {
    def isSimpleComparison(e: Expr): Boolean = e match {
      case GreaterThan(_,_) | GreaterEquals(_,_) | LessThan(_,_) | LessEquals(_,_) => true
      case _ => false
    }

    def totalUncert(l: Expr, r: Expr): Rational = {
      val lhsUncert = approximator.computeError(idealToActual(l, variables), precondition, variables, false)
      val rhsUncert = approximator.computeError(idealToActual(r, variables), precondition, variables, false)
      abs(rhsUncert - lhsUncert)
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

    val clauses = c1 match {
      case And(args) => args
      case x => Seq(x)
    }

    // TODO: handle the other constraints

    if (clauses.forall(c => isSimpleComparison(c))) {
      val c1WithErrors = clauses.map(c => addErrors(c))
      
      val constraintX2 = And(And(c1WithErrors), c2) 
      val z3Constraint = leonToZ3.getZ3Condition(constraintX2)

      //computeInterval
      // This would go even more accurate, if we did this altogether, 
      // essentially performing constraint propagation

      if (solver.isFeasible(z3Constraint, reporter)) {

        val cMap: Map[Expr, RationalInterval] = variables.inputs.map({
          case (v @ Variable(_), Record(i, a, Some(lo), Some(hi), Some(err), None)) =>
            val interval = solver.tightenRange(v, z3Constraint,
              RationalInterval(lo - err, hi + err), solverMaxIterHigh, solverPrecisionHigh)
            (v, interval)
        })

        Some(constraintX2, cMap)
      } else {
        None
      }
    } else {
      throw new Exception("Cannot handle this branch condition for path error computation: " + c1)
      None
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