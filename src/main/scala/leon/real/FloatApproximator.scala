/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Common._
//import purescala.Trees._
import purescala.Trees.{Expr, Variable, And, Equals, LessEquals, LessThan, GreaterThan, GreaterEquals}
import purescala.TreeOps._
import purescala.TypeTrees._

import real.Trees._
import real.TreeOps._
import XFloat._
import XFixed._
import Rational._
import VariableShop._

object FloatApproximator {

  // Just so we have it somewhere, not tested
  def evalWithError(reporter: Reporter, solver: RealSolver, precision: Precision, expr: Expr, precondition: Expr, inputs: VariablePool): Map[Expr, XReal] = {
    //val config = XFloatConfig(reporter, solver, precondition, options.defaultPrecision, getUnitRoundoff(options.defaultPrecision),
    //  solverMaxIterMedium, solverPrecisionMedium)

    val transformer = new FloatApproximator(reporter, solver, precision, precondition, inputs)
    transformer.transform(expr)

    transformer.variables -- inputs.actualVariables
  }

  var pathErrorVerbose = false
}

class FloatApproximator(reporter: Reporter, solver: RealSolver, precision: Precision, precondition: Expr, inputs: VariablePool,
  checkPathError: Boolean = true) extends TransformerWithPC {
  import FloatApproximator._

  implicit val debugSection = DebugSectionVerification

  type C = Seq[Expr]
  val initC = Nil

  val verboseLocal = false // TODO figure out which verbose that is if we call this 'verbose'
  val compactingThreshold = 200

  val leonToZ3 = new LeonToZ3Transformer(inputs, precision)
  val noiseRemover = new NoiseRemover
  val (minVal, maxVal) = precision.range 

  val (maxNegNormal, minPosNormal) = (-precision.minNormal, precision.minNormal)
  
  val initialCondition: Expr = leonToZ3.getZ3Expr(noiseRemover.transform(precondition))

  val config = XConfig(solver, initialCondition, solverMaxIterMedium, solverPrecisionMedium)

  val (machineEps, bits) = precision match {
    case FPPrecision(bts) => (Rational.zero, bts)
    case _ => (getUnitRoundoff(precision), 0)
  }

  if (verboseLocal) println("initial config: " + config)

  var variables: Map[Expr, XReal] = precision match {
    case Float32 | Float64 | DoubleDouble | QuadDouble => variables2xfloats(inputs, config, machineEps)._1
    case FPPrecision(bits) => variables2xfixed(inputs, config, bits)._1
  }

  if (verboseLocal) println("initial variables: " + variables)
  
  def register(e: Expr, path: C) = e match {
    // We allow only these conditions in if-then-else
    case LessThan(_,_) | LessEquals(_,_) | GreaterThan(_,_) | GreaterEquals(_,_) =>
      path :+ e
    case _ => path
  }

  def transformWithSpec(e: Expr): (Expr, Option[Spec]) = {
    val exprTransformed = this.transform(e)
    variables.get(FResVariable()) match {
      case Some(resXFloat) =>
        val spec = Spec(RationalInterval(resXFloat.realInterval.xlo, resXFloat.realInterval.xhi), resXFloat.maxError)
        (exprTransformed, Some(spec))
      case None =>
        (exprTransformed, None)
    }    
  }

  override def rec(e: Expr, path: C) =  {
    // TODO: ugly!
    def getXReal(e: Expr): XReal = e match {
      case ApproxNode(x) => x
      case fl: FloatLiteral => addCondition(fl, path)
      case v: Variable => addCondition(v, path)
      case And(args) => getXReal(args.last)
    }

    // the float condition is to be used with the negation of the actual condition to get only 
    // the values that are off-path
    def getOffPathConditions(cond: Expr): (Expr, Expr) = {
      def getTotalError(l: Expr, r: Expr): Expr = {
        val lActual = idealToActual(l, inputs)
        val rActual = idealToActual(r, inputs)
        
        val errLeft = getXReal(rec(lActual, path)).maxError
        val errRight = getXReal(rec(rActual, path)).maxError
        RealLiteral(errLeft + errRight)
      }

      cond match {
        case LessThan(l, r) =>
          val totalError = getTotalError(l, r)
          val floatCond = LessThan(l, PlusR(r, totalError))
          val realCond = GreaterEquals(l, MinusR(r, totalError))
          (floatCond, realCond)

        case LessEquals(l, r) =>
          val totalError = getTotalError(l, r)
          val floatCond = LessEquals(l, PlusR(r, totalError))
          val realCond = GreaterThan(l, MinusR(r, totalError))
          (floatCond, realCond)

        case GreaterThan(l, r) =>
          val totalError = getTotalError(l, r)
          val floatCond = GreaterThan(l, MinusR(r, totalError))
          val realCond = LessEquals(l, PlusR(r, totalError))
          (floatCond, realCond)

        case GreaterEquals(l, r) =>
          val totalError = getTotalError(l, r)
          val floatCond = GreaterEquals(l, MinusR(r, totalError))
          val realCond = LessThan(l, PlusR(r, totalError))
          (floatCond, realCond)
      }
    }// end getOffPathConditions


    // Computes the path error for one direction and branch 
    //@param branchCondition real-valued
    //@param f1 path to be taken by ideal execution
    //@param f2 path to be taken by floating-point execution
    def computePathError(currentPathCondition: Seq[Expr], branchCondition: Expr, f1: Expr, f2: Expr): Rational = {
      def removeErrors(xf: XReal): XReal = xf match {
        case xff: XFloat =>
          new XFloat(xff.tree, xff.approxInterval, new XRationalForm(Rational.zero), xff.config, xff.machineEps)  
        case xfp: XFixed =>
          new XFixed(xfp.format, xfp.tree, xfp.approxInterval, new XRationalForm(Rational.zero), xfp.config)
      }

      def addConditionToXReal(xf: XReal, condition: Expr): XReal = xf match {
        case xff: XFloat =>
          new XFloat(xff.tree, xff.approxInterval, xff.error, xff.config.addCondition(condition), xff.machineEps)
        case xfp: XFixed =>
          new XFixed(xfp.format, xfp.tree, xfp.approxInterval, xfp.error, xfp.config.addCondition(condition))
      }

      if (pathErrorVerbose) println("--------\n computing path error for condition: " + branchCondition)
      if (pathErrorVerbose) println("real path: "+ f1)
      if (pathErrorVerbose) println("actual path: "+f2)

      //([c], errc) = evalWithError(pre, c)
      val (flCond, reCond) = getOffPathConditions(branchCondition)
      
      val floatCondition = And(flCond, negate(branchCondition))
      val realCondition = And(reCond, branchCondition)
      if (pathErrorVerbose) println("floatCondition: %s\nrealCondition: %s".format(floatCondition, realCondition))
  
      //println("----> feasible? " + isFeasible(Seq(initialCondition, floatCondition)))
      //println(isFeasible(Seq(initialCondition, realCondition)))

      if (isFeasible(currentPathCondition :+ floatCondition) && isFeasible(currentPathCondition :+ realCondition)) {

        val variablesOfPaths = variablesOf(f1) ++ variablesOf(f2)
        
        //[f1]real = getRange(pre ∧ c(x) ∈ [−errc, 0], f1)
        val (freshMapReal, inputs1) = getFreshVariablesWithConditionWithoutErrors(variablesOfPaths, realCondition)
        if (pathErrorVerbose) println("freshMapReal: " + freshMapReal + "\ninputs1:")
        if (pathErrorVerbose) inputs1.foreach{ i => println(i.toString + " " + i._2.config)}

        variables = variables ++ inputs1
        solver.clearCounts
        //XFloat.verbose = true
        // don't add the branchCondition to the path, since it's in terms of real variables and will cause an invalid result
        // the branchCondition is already added to the config of the variables, and for constants it doesn't matter
        //println("realPath: " + replace(freshMapReal, f1))
        val realResult = getXReal(rec(replace(freshMapReal, f1), path))
        //println("real result config: " + realResult.config.getCondition)
        //println("real result: " + realResult)
        //println("solverPrecision: " + realResult.config.solverPrecision)
        if (pathErrorVerbose) println("realResult: " + removeErrors(realResult))
        
        
        //([f2]float, errfloat) = evalWithError(pre ∧ c(x) ∈ [0, errc], f2)
        //(Map[Expr, Expr], Map[Expr, XFloat])
        val (freshMapFloat, inputs2) = getFreshVariablesWithConditionWithoutErrors(variablesOfPaths, floatCondition)
        if (pathErrorVerbose) println("freshMapFloat: " + freshMapFloat + "\ninputs2: ")
        //if (pathErrorVerbose) inputs2.foreach{ i => println(i.toString + " " + i._2.config) }

        variables = variables ++ inputs2
        solver.clearCounts
        val floatResult = getXReal(rec(replace(freshMapFloat, f2), path))
        //println("floatResult: " + floatResult)


        //return: max |[f1]real − ([f2]float + errfloat)|
        val correlation = variables.filter { x => x._1 match {
              case Variable(id) => variablesOfPaths.contains(id)
              case _ => false
            }}.map {
          case (v, xf) =>
            val freshErrorVar = getNewErrorVar
            And(Seq(Equals(freshMapFloat(v), PlusR(freshMapReal(v), freshErrorVar)),
            LessEquals(RealLiteral(-xf.maxError), freshErrorVar),
            LessEquals(freshErrorVar, RealLiteral(xf.maxError))))
          }
        if (pathErrorVerbose) println("correlation: " + correlation)
      
        val realResultWithCorrelation = addConditionToXReal(removeErrors(realResult), And(correlation.toSeq))
          //new XFloat(realResult.tree, realResult.approxInterval, new XRationalForm(Rational.zero),
          //realResult.config.addCondition(And(correlation.toSeq)))
        if (pathErrorVerbose) println("realResultWithCorrelation: " + realResultWithCorrelation)
        //println("\n realRangeWithCorrelation.config" + realResultWithCorrelation.config.getCondition)

        //println("floatResult.config: " + floatResult.config.getCondition)
        solver.clearCounts
        //XFloat.verbose = true
        val diffXFloat = (floatResult - realResultWithCorrelation)
        val diff = diffXFloat.interval
        if (pathErrorVerbose) println("diff: " + diff)
        //println("diff config: " + diffXFloat.config.getCondition)
        if (pathErrorVerbose) reporter.info("STATS for diff: " + solver.getCounts)
        //XFloat.verbose = false
        // restore state from before
        variables = variables -- inputs1.keys -- inputs2.keys
        //XFloat.verbose = false
        val maxError = max(abs(diff.xlo), abs(diff.xhi))
        if (pathErrorVerbose) println("maxError: " + maxError)
        maxError

      } else {
        reporter.debug("Other path not feasible")
        Rational.zero
      }
    }
    
        
    val newExpr = e match {
      case EqualsF(lhs, rhs) =>
        val x = getXReal(rec(rhs, path))
        variables = variables + (lhs -> x)
        constraintFromXFloats(Map(lhs -> x))

      // TODO: do we need this? this should only appear in the postcondition which we do not evaluate
      //case InitialNoise(v @ Variable(_)) => vars(v).maxError
      case UMinusF(t) =>        ApproxNode(-getXReal(rec(t, path)))
      case PlusF(lhs, rhs) =>   ApproxNode(getXReal(rec(lhs, path)) + getXReal(rec(rhs, path)))
      case MinusF(lhs, rhs) =>  ApproxNode(getXReal(rec(lhs, path)) - getXReal(rec(rhs, path)))
      case TimesF(lhs, rhs) =>  ApproxNode(getXReal(rec(lhs, path)) * getXReal(rec(rhs, path)))
      case DivisionF(lhs, rhs) =>
        val r = getXReal(rec(rhs, path))
        if (possiblyZero(r.interval)) throw RealArithmeticException("Potential div-by-zero detected: " + e)
        ApproxNode(getXReal(rec(lhs, path)) / r)
        
      case SqrtF(t) =>
        val x = getXReal(rec(t, path))
        if (possiblyNegative(x.interval)) throw RealArithmeticException("Potential sqrt of negative detected: " + e)
        ApproxNode(x.squareRoot)    
        
      case FloatIfExpr(cond, thenn, elze) =>
        val currentPathCondition = path :+ initialCondition
        val thenBranch =
          if (isFeasible(currentPathCondition :+ cond)) Some(getXReal(rec(thenn, register(cond, path))))
          else None

        val elseBranch =
          if (isFeasible(currentPathCondition :+ negate(cond))) Some(getXReal(rec(elze, register(negate(cond), path))))
          else None
        assert(!thenBranch.isEmpty || !elseBranch.isEmpty)
        reporter.debug("thenBranch: " + thenBranch)
        reporter.debug("elseBranch: " + elseBranch)


        val pathError = if (checkPathError) { // When the actual computation goes a different way than the real one
          val pathError1 = computePathError(currentPathCondition, cond, thenn, elze)
          reporter.debug("computed error 1: " + pathError1)

          val pathError2 = computePathError(currentPathCondition, negate(cond), elze, thenn)
          reporter.debug("computed error 2: " + pathError1)

          max(pathError1, pathError2)
        } else {
          zero
        }
        ApproxNode(mergeXRealWithExtraError(thenBranch, elseBranch, And(path), pathError))

      case FncValueF(spec) =>
        val (interval, error, constraints) = getResultSpec(spec)
        val fresh = getNewXFloatVar

        val tmp = precision match {
          case FPPrecision(bts) => ApproxNode(xFixedWithUncertain(fresh, interval,
            config.addCondition(replace(Map(ResultVariable() -> fresh), leonToZ3.getZ3Condition(noiseRemover.transform(spec)))),
            error, false, bts)._1)
          case _ => ApproxNode(xFloatWithUncertain(fresh, interval,
            config.addCondition(replace(Map(ResultVariable() -> fresh), leonToZ3.getZ3Condition(noiseRemover.transform(spec)))),
            error, false, machineEps)._1)
        }
        tmp

      case FncBodyF(name, body) =>
        val fncValue = rec(body, path)
        ApproxNode(getXReal(fncValue))

      case _ =>
        super.rec(e, path)
    }
    newExpr match {
      case ApproxNode(x) if (overflowPossible(x.interval)) =>
        reporter.warning("Possible overflow detected at: " + newExpr)
        newExpr
      case ApproxNode(x) if (denormal(x.interval)) =>
        throw RealArithmeticException("Denormal value detected for " + e)
        null
      case ApproxNode(x) if (formulaSize(x.tree) > compactingThreshold) =>
        reporter.warning("compacting, size: " + formulaSize(x.tree))
        val fresh = getNewXFloatVar
        ApproxNode(compactXFloat(x, fresh))

      case _ =>
        newExpr
    }
  }
  
  private def compactXFloat(xreal: XReal, newTree: Expr): XReal = {
    val newConfig = xreal.config.addCondition(rangeConstraint(newTree, xreal.realInterval))
    val (newXReal, index) = xreal match {  
      case xf: XFloat =>
        xFloatWithUncertain(newTree, xreal.approxInterval, newConfig, xreal.maxError, false, xf.machineEps)
      //v: Expr, range: RationalInterval, config: XConfig,uncertain: Rational, withRoundoff: Boolean, bits: Int
      case xfp: XFixed =>
        xFixedWithUncertain(newTree, xreal.approxInterval, newConfig, xreal.maxError, false, xfp.format.bits)
    }
    newXReal
  }



  // TODO: this has to be done better, perhaps use monads
  //@param (freshMap, xfloatMap) freshMap is the map from existing variables to fresh ones, 
  // xfloatMap is the map from new variables to xfloats without errors
  private def getFreshVariablesWithConditionWithoutErrors(vars: Set[Identifier], cond: Expr): (Map[Expr, Expr], Map[Expr, XReal]) = {
    
    var freshMap: Map[Expr, Expr] = variables.collect {
      case (v @ Variable(id), xf) if (vars.contains(id)) => (v, getFreshVarOf(id.toString))
    }
    //ideal to new variables
    var buddyFreshMap: Map[Expr, Expr] = variables.collect {
      case (v @ Variable(id), xf) if (vars.contains(id)) => (inputs.getIdeal(v), freshMap(v))
    }
    
    val newInputs =
      freshMap.map {
      case (v, fresh) =>
        val xf = variables(v)
        // TODO: add the condition before to improve the approx interval?
        precision match {
          case FPPrecision(bits) =>
            // TODO: format needs to be determined with range
            (fresh, new XFixed(???, replace(buddyFreshMap, xf.tree), xf.approxInterval, new XRationalForm(Rational.zero),
              xf.config.addCondition(cond).freshenUp(buddyFreshMap).updatePrecision(solverMaxIterHigh, solverPrecisionHigh)))

          case _ =>
            (fresh, new XFloat(replace(buddyFreshMap, xf.tree), xf.approxInterval, new XRationalForm(Rational.zero),
              xf.config.addCondition(cond).freshenUp(buddyFreshMap).updatePrecision(solverMaxIterHigh, solverPrecisionHigh), machineEps))
        }
    }
    (freshMap, newInputs)
  }
  
  private def mergeXRealWithExtraError(one: Option[XReal], two: Option[XReal], condition: Expr,
    pathError: Rational): XReal = (one, two) match {
    case (Some(x1), Some(x2)) =>
      val newInt = x1.realInterval.union(x2.realInterval)
      val newError = max(max(x1.maxError, x2.maxError), pathError)
      val fresh = getNewXFloatVar
      val newConfig = config.addCondition(leonToZ3.getZ3Condition(And(condition, rangeConstraint(fresh, newInt))))
      precision match {
        case FPPrecision(bts) => xFixedWithUncertain(fresh, newInt, newConfig, newError, false, bts)._1
        case _ => xFloatWithUncertain(fresh, newInt, newConfig, newError, false, machineEps)._1
      }
    case (Some(x1), None) =>
      if (pathError != zero) {
        val newError = max(x1.maxError, pathError)
        val newInt = x1.realInterval
        val fresh = getNewXFloatVar
        val newConfig = config.addCondition(leonToZ3.getZ3Condition(And(condition, rangeConstraint(fresh, newInt))))
        precision match {
          case FPPrecision(bts) => xFixedWithUncertain(fresh, newInt, newConfig, newError, false, bts)._1
          case _ => xFloatWithUncertain(fresh, newInt, newConfig, newError, false, machineEps)._1
        }
      } else
        x1
    case (None, Some(x2)) =>
      if (pathError != zero) {
        val newError = max(x2.maxError, pathError)
        val newInt = x2.realInterval
        val fresh = getNewXFloatVar
        val newConfig = config.addCondition(leonToZ3.getZ3Condition(And(condition, rangeConstraint(fresh, newInt))))
        precision match {
          case FPPrecision(bts) => xFixedWithUncertain(fresh, newInt, newConfig, newError, false, bts)._1
          case _ => xFloatWithUncertain(fresh, newInt, newConfig, newError, false, machineEps)._1
        }
      } else
        x2
    // We assume that one of the two branches is feasible
    case (None, None) =>
      throw new Exception("One of the paths should be feasible")
      null
  }

  private def rangeConstraint(v: Expr, i: RationalInterval): Expr = {
    // FIXME: check this (RealLiteral or FloatLiteral?)
    And(LessEquals(RealLiteral(i.xlo), v), LessEquals(v, RealLiteral(i.xhi)))
  }
  

  private def constraintFromXFloats(results: Map[Expr, XReal]): Expr = {
    And(results.foldLeft(Seq[Expr]())(
      (seq, kv) => seq ++ Seq(LessEquals(RealLiteral(kv._2.interval.xlo), kv._1),
                                LessEquals(kv._1, RealLiteral(kv._2.interval.xhi)),
                                Noise(inputs.getIdeal(kv._1), RealLiteral(kv._2.maxError)))))
    /*(seq, kv) => seq ++ Seq(LessEquals(RealLiteral(kv._2.realInterval.xlo), inputs.getIdeal(kv._1)),
                                LessEquals(inputs.getIdeal(kv._1), RealLiteral(kv._2.realInterval.xhi)),
                                Noise(inputs.getIdeal(kv._1), RealLiteral(kv._2.maxError)))))*/
  }

  private def overflowPossible(interval: RationalInterval): Boolean = interval.xlo < minVal || maxVal < interval.xhi
  
  private def possiblyZero(interval: RationalInterval): Boolean = interval.xlo < Rational.zero && interval.xhi > Rational.zero

  private def possiblyNegative(interval: RationalInterval): Boolean = interval.xlo < Rational.zero || interval.xhi < Rational.zero

  // tests if the entire interval lies in the denormal range
  private def denormal(interval: RationalInterval): Boolean = precision match {
    case FPPrecision(_) => false
    case _ => (maxNegNormal < interval.xlo && interval.xhi < minPosNormal)
  }
    
  private def addCondition(v: Expr, cond: Seq[Expr]): XReal = {
    v match {
      case v: Variable =>
        variables(v) match {
          case xfl: XFloat => new XFloat(xfl.tree, xfl.approxInterval, xfl.error, xfl.config.addCondition(leonToZ3.getZ3Condition(And(cond))), machineEps)
          case xfx: XFixed => new XFixed(xfx.format, xfx.tree, xfx.approxInterval, xfx.error, xfx.config.addCondition(leonToZ3.getZ3Condition(And(cond))))
        }

      case FloatLiteral(r, exact) =>
        precision match {
          case FPPrecision(bits) => XFixed(r, config.addCondition(leonToZ3.getZ3Condition(And(cond))), bits)
          case _ => XFloat(r, config.addCondition(leonToZ3.getZ3Condition(And(cond))), machineEps) // TODO: save the machineEps somewhere?
        }
    }
  }

  /*private def addCondition(v: XReal, cond: Seq[Expr]): XReal = {
    if (cond.size > 0)
      new XFloat(v.tree, v.approxInterval, v.error, v.config.addCondition(leonToZ3.getZ3Condition(And(cond))))
    else
      v
  }*/

  private def isFeasible(pre: Seq[Expr]): Boolean = {
    import Sat._
    solver.checkSat(leonToZ3.getZ3Expr(And(pre))) match {
      case (SAT, model) => true
      case (UNSAT, model) => false
      case _ =>
        reporter.info("Sanity check failed! ")// + sanityCondition)
        false
    }
  }
}
  
  /*
  private def sanityCheck(pre: Expr, silent: Boolean = true): Boolean = {
    import Sat._
    solver.checkSat(pre) match {
      case (SAT, model) =>
        if (!silent) reporter.info("Sanity check passed! :-)")
        //reporter.info("model: " + model)
        true
      case (UNSAT, model) =>
        if (!silent) reporter.warning("Not sane! " + pre)
        false
      case _ =>
        reporter.info("Sanity check failed! ")// + sanityCondition)
        false
    }
  }
  */
