/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Common._
import purescala.Trees.{Expr, Variable, And, Equals, LessEquals, LessThan, GreaterThan, GreaterEquals, BooleanLiteral}
import purescala.TreeOps._
import purescala.TypeTrees._

import real.Trees._
import real.TreeOps._
import XFloat._
import XFixed._
import Rational._
import VariableShop._

class Approximator(reporter: Reporter, solver: RealSolver, precision: Precision, precondition: Expr, inputs: VariablePool,
  checkPathError: Boolean = true) {

  implicit val debugSection = DebugSectionVerification
  val verbose = false
  var pathErrorVerbose = false
  val compactingThreshold = 200
  val (minVal, maxVal) = precision.range 
  val (maxNegNormal, minPosNormal) = (-precision.minNormal, precision.minNormal)
  val (machineEps, bits) = precision match {
    case FPPrecision(bts) => (Rational.zero, bts)
    case _ => (getUnitRoundoff(precision), 0)
  }

  val leonToZ3 = new LeonToZ3Transformer(inputs, precision)
  val noiseRemover = new NoiseRemover
  
  val initialCondition: Expr = leonToZ3.getZ3Expr(noiseRemover.transform(precondition))
  val config = XConfig(solver, initialCondition, solverMaxIterMedium, solverPrecisionMedium)
  if (verbose) println("initial config: " + config)

  var variables: Map[Expr, XReal] = precision match {
    case Float32 | Float64 | DoubleDouble | QuadDouble => variables2xfloats(inputs, config, machineEps)._1
    case FPPrecision(bits) => variables2xfixed(inputs, config, bits)._1
  }
  if (verbose) println("initial variables: " + variables)

  // returned from Equals, but not used
  val dummyXReal = new XReal(RealLiteral(zero), RationalInterval(zero, zero), XRationalForm(zero, collection.mutable.Queue()), config)

  private def constraintFromXFloats(results: Map[Expr, XReal]): Expr = {
      And(results.foldLeft(Seq[Expr]())(
        (seq, kv) => seq ++ Seq(LessEquals(RealLiteral(kv._2.interval.xlo), kv._1),
                                LessEquals(kv._1, RealLiteral(kv._2.interval.xhi)),
                                Noise(inputs.getIdeal(kv._1), RealLiteral(kv._2.maxError)))))
  }

  /* 'generateFullConstraint' will ignore the returned approximation and generate a constraint
     over all (intermediate) variables. This mode should be used for checking pre-conditions.
    @return (computed constraint, spec of the result, if applicable)
   */
  def transformWithSpec(e: Expr, generateFullConstraint: Boolean): (Expr, Option[Spec]) = {
    def constraintFromXFloats(results: Map[Expr, XReal]): Expr = {
      And(results.foldLeft(Seq[Expr]())(
        (seq, kv) => seq ++ Seq(LessEquals(RealLiteral(kv._2.interval.xlo), kv._1),
                                LessEquals(kv._1, RealLiteral(kv._2.interval.xhi)),
                                Noise(inputs.getIdeal(kv._1), RealLiteral(kv._2.maxError)))))
    }
    e match {
      case BooleanLiteral(_) => (e, None)  // if no body
      case _ =>
        val approximation = approx(e, Seq())

        // sanityCheck
        //if

        if (generateFullConstraint) {
          (constraintFromXFloats(variables), None)
        } else {
          val spec = Spec(inputs.resultVar.id, RationalInterval(approximation.realInterval.xlo, approximation.realInterval.xhi),
                          approximation.maxError)
          (constraintFromXFloats(Map(inputs.fResultVar -> approximation)), Some(spec))
        }
    }    
  }

  private def register(path: Seq[Expr], e: Expr) = e match {
    // We allow only these conditions in if-then-else
    case LessThan(_,_) | LessEquals(_,_) | GreaterThan(_,_) | GreaterEquals(_,_) =>
      path :+ e
    case _ => path
  }

  def approx(e: Expr, path: Seq[Expr]): XReal = {
    // the float condition is to be used with the negation of the actual condition to get only 
    // the values that are off-path
    def getOffPathConditions(cond: Expr): (Expr, Expr) = {
      def getTotalError(l: Expr, r: Expr): Expr = {
        val lActual = idealToActual(l, inputs)
        val rActual = idealToActual(r, inputs)
        
        val errLeft = approx(lActual, path).maxError
        val errRight = approx(rActual, path).maxError
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
        val realResult = approx(replace(freshMapReal, f1), path)
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
        val floatResult = approx(replace(freshMapFloat, f2), path)
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

    (e match {
      case EqualsF(lhs, rhs) =>
        val x = approx(rhs, path)
        variables = variables + (lhs -> x)
        dummyXReal // this won't be used, but we need to return something 

      case UMinusF(t) =>        - approx(t, path)
      case PlusF(lhs, rhs) =>   approx(lhs, path) + approx(rhs, path)
      case MinusF(lhs, rhs) =>  approx(lhs, path) - approx(rhs, path)
      case TimesF(lhs, rhs) =>  approx(lhs, path) * approx(rhs, path)
      case DivisionF(lhs, rhs) =>
        val r = approx(rhs, path)
        if (possiblyZero(r.interval)) throw RealArithmeticException("Potential div-by-zero detected: " + e)
        approx(lhs, path) / r
          
      case SqrtF(t) =>
        val x = approx(t, path)
        if (possiblyNegative(x.interval)) throw RealArithmeticException("Potential sqrt of negative detected: " + e)
        x.squareRoot
          
      case FloatIfExpr(cond, thenn, elze) =>
        val currentPathCondition = path :+ initialCondition
        val notCond = negate(cond)
        val thenBranch =
          if (isFeasible(currentPathCondition :+ cond)) Some(approx(thenn, register(path, cond)))
          else None

        val elseBranch =
          if (isFeasible(currentPathCondition :+ notCond)) Some(approx(elze, register(path, notCond)))
          else None
        assert(!thenBranch.isEmpty || !elseBranch.isEmpty)
        reporter.debug("thenBranch: " + thenBranch)
        reporter.debug("elseBranch: " + elseBranch)


        val pathError = if (checkPathError) { // When the actual computation goes a different way than the real one
          val pathError1 = computePathError(currentPathCondition, cond, thenn, elze)
          reporter.debug("computed error 1: " + pathError1)

          val pathError2 = computePathError(currentPathCondition, notCond, elze, thenn)
          reporter.debug("computed error 2: " + pathError1)

          max(pathError1, pathError2)
        } else {
          zero
        }
        mergeXRealWithExtraError(thenBranch, elseBranch, And(path), pathError)

      case FncValueF(spec, specExpr) =>
        val (resId, interval, error, constraints) = (spec.id, spec.bounds, spec.absError, True) // constraints not (yet) used
        val fresh = getNewXFloatVar

        precision match {
          case FPPrecision(bts) => xFixedWithUncertain(fresh, interval,
            config.addCondition(replace(Map(Variable(resId) -> fresh), leonToZ3.getZ3Condition(noiseRemover.transform(specExpr)))),
            error, false, bts)._1
          case _ => xFloatWithUncertain(fresh, interval,
            config.addCondition(replace(Map(Variable(resId) -> fresh), leonToZ3.getZ3Condition(noiseRemover.transform(specExpr)))),
            error, false, machineEps)._1
        }

      case FncBodyF(name, body) => approx(body, path)
      
      case fl: FloatLiteral => addCondition(fl, path)
      case v: Variable => addCondition(v, path)
      
      case And(es) => {
        val allEs = for(ex <- es) yield approx(ex, path)
        allEs.last
      }

    }) match {
      case x: XReal if (overflowPossible(x.interval)) => reporter.warning("Possible overflow detected at: " + x); x
      case x: XReal if (denormal(x.interval)) => throw RealArithmeticException("Denormal value detected for " + e); null
      case x: XReal if (formulaSize(x.tree) > compactingThreshold) =>
        reporter.warning("compacting, size: " + formulaSize(x.tree))
        val fresh = getNewXFloatVar
        compactXFloat(x, fresh)
      case x => x
    }
  }


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
        precision match {
          case FPPrecision(bits) =>
            (fresh, new XFixed(xf.asInstanceOf[XFixed].format, replace(buddyFreshMap, xf.tree), xf.approxInterval, new XRationalForm(Rational.zero),
              xf.config.addCondition(cond).freshenUp(buddyFreshMap).updatePrecision(solverMaxIterHigh, solverPrecisionHigh)))

          case _ =>
            (fresh, new XFloat(replace(buddyFreshMap, xf.tree), xf.approxInterval, new XRationalForm(Rational.zero),
              xf.config.addCondition(cond).freshenUp(buddyFreshMap).updatePrecision(solverMaxIterHigh, solverPrecisionHigh), machineEps))
        }
    }
    (freshMap, newInputs)
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
          case _ => XFloat(r, config.addCondition(leonToZ3.getZ3Condition(And(cond))), machineEps)
        }
    }
  }

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

  private def rangeConstraint(v: Expr, i: RationalInterval): Expr = {
    // FIXME: check this (RealLiteral or FloatLiteral?)
    And(LessEquals(RealLiteral(i.xlo), v), LessEquals(v, RealLiteral(i.xhi)))
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

  

  private def compactXFloat(xreal: XReal, newTree: Expr): XReal = {
    val newConfig = xreal.config.addCondition(rangeConstraint(newTree, xreal.realInterval))
    val (newXReal, index) = xreal match {  
      case xf: XFloat =>
        xFloatWithUncertain(newTree, xreal.approxInterval, newConfig, xreal.maxError, false, xf.machineEps)
      case xfp: XFixed =>
        xFixedWithUncertain(newTree, xreal.approxInterval, newConfig, xreal.maxError, false, xfp.format.bits)
    }
    newXReal
  }

  private def overflowPossible(interval: RationalInterval): Boolean = interval.xlo < minVal || maxVal < interval.xhi

  private def possiblyZero(interval: RationalInterval): Boolean = interval.xlo < Rational.zero && interval.xhi > Rational.zero

  private def possiblyNegative(interval: RationalInterval): Boolean = interval.xlo < Rational.zero || interval.xhi < Rational.zero

  // tests if the entire interval lies in the denormal range
  private def denormal(interval: RationalInterval): Boolean = precision match {
    case FPPrecision(_) => false
    case _ => (interval.xlo != interval.xhi && maxNegNormal < interval.xlo && interval.xhi < minPosNormal)
  }
}