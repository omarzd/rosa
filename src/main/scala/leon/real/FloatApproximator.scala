/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

import real.Trees._
import real.TreeOps._
import XFloat._

object FloatApproximator {

  // Just so we have it somewhere, not tested
  def evalWithError(solver: RealSolver, options: RealOptions, expr: Expr, precondition: Expr, inputs: VariablePool): Map[Expr, XFloat] = {
    //val config = XFloatConfig(reporter, solver, precondition, options.defaultPrecision, getUnitRoundoff(options.defaultPrecision),
    //  solverMaxIterMedium, solverPrecisionMedium)

    val transformer = new FloatApproximator(solver, options, precondition, inputs)
    transformer.transform(expr)

    transformer.variables -- inputs.actualVariables
  }

}

class FloatApproximator(solver: RealSolver, options: RealOptions,
  precondition: Expr, inputs: VariablePool) extends TransformerWithPC {
  type C = Seq[Expr]
  val initC = Nil

  val leonToZ3 = new LeonToZ3Transformer(inputs)
    
  val config = XFloatConfig(solver, leonToZ3.getZ3Expr(precondition, options.defaultPrecision), 
    options.defaultPrecision, getUnitRoundoff(options.defaultPrecision),
    solverMaxIterMedium, solverPrecisionMedium)

  var variables: Map[Expr, XFloat] = variables2xfloats(inputs, config)._1
  def register(e: Expr, path: C) = path :+ e

  override def rec(e: Expr, path: C) = e match {
    case Equals(lhs, rhs) if (rhs.getType == FloatType) =>
      // evaluate the rhs
      val evalRhs = evalArith(rhs)
      variables = variables + (lhs -> evalRhs)
      println("evaluating: " + e)
      println("with result: " + evalRhs)
      constraintFromXFloats(Map(lhs -> evalRhs))

    // TODO: If-then-else

    case _ =>
      super.rec(e, path)
  }

    // Evaluates an arithmetic expression
    //TODO: checks for overflow and such here
    /*
// Check for potential overflow
  config.precision match {
    case Float32 =>
      if (interval.xlo < -MaxFloat || MaxFloat < interval.xhi) {
        config.reporter.warning("Potential overflow detected for: %s,\nwith precondition %s".format(tree, config.precondition))
      }
    case Float64 =>
      if (interval.xlo < -MaxDouble || MaxDouble < interval.xhi) {
        config.reporter.warning("Potential overflow detected for: %s,\nwith precondition %s".format(tree, config.precondition))
        config.reporter.info(interval)
      }
    case DoubleDouble => // same range as Double
      if (interval.xlo < -MaxDouble || MaxDouble < interval.xhi) {
        config.reporter.warning("Potential overflow detected for: %s,\nwith precondition %s".format(tree, config.precondition))
        config.reporter.info(interval)
      }
    case QuadDouble => // same range as Double
      if (interval.xlo < -MaxDouble || MaxDouble < interval.xhi) {
        config.reporter.warning("Potential overflow detected for: %s,\nwith precondition %s".format(tree, config.precondition))
        config.reporter.info(interval)
      }
  }

  if (y.interval.xlo < Rational.zero && y.interval.xhi > Rational.zero) {
      config.reporter.warning("Potential division by zero detected for: %s/%s,\nwith precondition %s".format(
        this.tree, y.tree, config.precondition))
      config.reporter.warning("y.interval: " + y.interval)
    }

    if (interval.xlo < Rational.zero || interval.xhi < Rational.zero) {
      config.reporter.warning("Potential square root of a negative number for: %s,\nwith precondition %s".format(
        this.tree, config.precondition))
      config.reporter.warning("interval: " + this.interval)
    }
    */

  private def evalArith(expr: Expr): XFloat = {
    val xfloat = expr match {
    case v @ Variable(id) => variables(v)
    case RationalLiteral(v) => XFloat(v, config)
    //case IntLiteral(v) => XFloat(v, config)
    case UMinusF(rhs) => - evalArith(rhs)
    case PlusF(lhs, rhs) => evalArith(lhs) + evalArith(rhs)
    case MinusF(lhs, rhs) => evalArith(lhs) - evalArith(rhs)
    case TimesF(lhs, rhs) => evalArith(lhs) * evalArith(rhs)
    case DivisionF(lhs, rhs) => evalArith(lhs) / evalArith(rhs)
    case SqrtF(t) => evalArith(t).squareRoot
    /*case FunctionInvocation(funDef, args) =>
        // Evaluate the function, i.e. compute the postcondition and inline it
      println("function call: " + funDef.id.toString)
      /*val fresh = getNewFncVariable(funDef.id.name)
      val arguments: Map[Expr, Expr] = funDef.args.map(decl => decl.toVariable).zip(args).toMap
      val newBody = replace(arguments, vcMap(funDef).body)
      val vals = inXFloats(reporter, newBody, vars, config)
      val result = vals._1(ResultVariable())
      val newXFloat = compactXFloat(result, fresh)
      newXFloat*/

      //In this version we inline the postcondition instead
      val fresh = getNewFncVariable(funDef.id.name)
      val arguments: Map[Expr, Expr] = funDef.args.map(decl => decl.toVariable).zip(args).toMap

      val firstChoice = funDef.postcondition
      val secondChoice = vcMap(funDef).generatedPost
      val post = firstChoice match {
        case Some(post) if (postComplete.check(post)) => Some(post)
        case _ => secondChoice match {
          case Some(post) if (postComplete.check(post)) => Some(post)
          case _ => None
        }
      }
      println("post: " + post)
      // there is no body to evaluate, but a new XFloat
      // Basically, we have to construct the new XFloat from the postcondition
      post match {
        case Some(p) =>
          val freshCondition = replace(arguments, p)
          resultCollector.getResultWithExpr(freshCondition) match {
            case Some((lo, hi, errorExpr)) =>
              println("errorExpr found: " + errorExpr)
              val newInt = RationalInterval(lo, hi)
              val newError = evalErrorExpr(errorExpr, vars)
              println("error evaluated: " + newError)
              val newConfig = config.addCondition(rangeConstraint(fresh, newInt))
              val xf = xFloatWithUncertain(fresh, newInt, newConfig, newError, false)._1
              println("returning: " + xf)
              xf
            case None =>
              throw UnsupportedFragmentException("Incomplete postcondition for: " + expr)
              null
          }
        case None =>
          throw UnsupportedFragmentException("Incomplete postcondition for: " + expr)
          null
      }
    */
    case _ => // FIXME: why don't we handle the two failures in the same way?
      throw UnsupportedRealFragmentException("XFloat cannot handle: " + expr)
      null
    }
      /*if (formulaSize(xfloat.tree) > compactingThreshold) {
        reporter.warning("compacting, size: " + formulaSize(xfloat.tree))
        val fresh = getNewXFloatVar
        compactXFloat(xfloat, fresh)
      } else {*/
        xfloat
      //}
  }

  private def constraintFromXFloats(results: Map[Expr, XFloat]): Expr = {
    And(results.foldLeft(Seq[Expr]())(
      (seq, kv) => seq ++ Seq(LessEquals(new RationalLiteral(kv._2.interval.xlo, true), kv._1),
                                LessEquals(kv._1, new RationalLiteral(kv._2.interval.xhi, true)),
                                Noise(inputs.getIdeal(kv._1), RationalLiteral(kv._2.maxError)))))
  }
}


  /*private def inXFloats(expr: Expr, vars: Map[Expr, XFloat], config: XFloatConfig): (Map[Expr, XFloat], Option[XFloat]) = {
    expr match {
      case And(args) =>
        var currentVars: Map[Expr, XFloat] = vars
        var lastXf: Option[XFloat] = None
        for (arg <- args) {
          val (map, xf) = inXFloats(arg, currentVars, config)
          lastXf = xf
          currentVars = map
          (currentVars, lastXf)
        }
        (currentVars, lastXf)

      case Equals(variable, value) =>
        val (map, computedValue) = inXFloats(value, vars, config)
        (vars + (variable -> computedValue.get), None)

      /*case IfExpr(cond, then, elze) =>
        // Errors and ranges from the two branches
        val thenConfig = config.addCondition(cond)
        val elzeConfig = config.addCondition(negate(cond))
        val (thenMap, thenValue) =
          if (sanityCheck(thenConfig.getCondition)) inXFloats(reporter, then, addConditionToInputs(vars, cond), thenConfig)
          else (vars, None)
        val (elzeMap, elzeValue) =
          if (sanityCheck(elzeConfig.getCondition))
            inXFloats(reporter, elze, addConditionToInputs(vars, negate(cond)), elzeConfig)
          else (vars, None)
        assert(!thenValue.isEmpty || !elzeValue.isEmpty)
        println("thenValue: " + thenValue)
        println("elzeValue: " + elzeValue)
        
        val pathError = if (checkPathError) {
          // When the actual computation goes a different way than the real one
          val (flCond1, reCond1) = getDiffPathsConditions(cond, vars, config)
          println("cond1: " + flCond1)
          val (flCond2, reCond2) = getDiffPathsConditions(negate(cond), vars, config)
          println("cond2: " + flCond2)

          val pathErrorThen = getPathError(elze, And(flCond1, negate(cond)), then, And(cond, reCond1), vars, config)
          println("pathError1: %.16g".format(pathErrorThen.toDouble))

          val pathErrorElze = getPathError(then, And(flCond2, cond), elze, And(negate(cond), reCond2), vars, config)
          println("pathError2: %.16g".format(pathErrorElze.toDouble))
          max(pathErrorThen, pathErrorElze)
        } else {
          zero
        }
        (vars, Some(mergeXFloatWithExtraError(thenValue, elzeValue, config, pathError)).get)
      */

      case Variable(_) | RationalLiteral(_) | UMinusF(_) | PlusF(_, _) | MinusF(_, _) | TimesF(_, _) | //IntLiteral(_) | 
        DivisionF(_, _) | SqrtF(_) | FunctionInvocation(_, _) =>
        (vars, Some(evalArith(expr, vars, config)))

      case BooleanLiteral(true) => (vars, None)
      case _ =>
        reporter.error("Xfloat cannot handle: " + expr)
        (Map.empty, None)
    }
  }*/

  /* ---------------------
      Error across paths
   ----------------------- */

  // The conditions are not fresh, we do that here automatically
  // TODO: this has a bug with function calls
  // TODO: this also has a bug if having local vars, the condition computation doesn't quite work
  /*private def getPathError(flExpr: Expr, flCond: Expr, reExpr: Expr, reCond: Expr, vars: Map[Expr, XFloat],
    config: XFloatConfig): Rational = {
    //println("flCond: " + flCond)
    //println("config: " + config)
    //TODO: check this
    if (sanityCheck(And(config.getCondition, flCond)) && sanityCheck(And(config.getCondition, reCond))) {
      // execution taken by actual computation
      val flConfig = config.addCondition(flCond).updatePrecision(solverMaxIterHigh, solverPrecisionHigh)
      //println("flConfig: " + flConfig.getCondition)
      //println("flExpr: " + flExpr)
      val flVars = addConditionToInputsAndRemoveErrors(vars, flCond)
      //println("fl vars:"); flVars.foreach {f => println(f)}
      solver.clearCounts
      val (m, floatRange) = inXFloats(reporter, flExpr, flVars, flConfig)
      //reporter.info("STATS for floatRange: " + solver.getCounts)
      //println("floatRange: " + floatRange)

      val freshMap = getFreshMap(vars.keySet)
      val (freshThen, freshVars) = freshenUp(reExpr, freshMap, vars)
      val reConfig = config.addCondition(reCond).freshenUp(freshMap).updatePrecision(solverMaxIterHigh, solverPrecisionHigh)
      val reVars = addConditionToInputsAndRemoveErrors(freshVars, replace(freshMap, reCond))
      //println("re vars:"); reVars.foreach {f => println(f._1 + "  " + f._2.config.getCondition)}
      solver.clearCounts
      val (mm, realRange) = inXFloats(reporter, freshThen, reVars, reConfig)
      //reporter.info("STATS for realRange: " + solver.getCounts)
      //println("realRange: "+ removeErrors(realRange.get))
      //println("realRange cond: " + realRange.get.config.getCondition)

      val correlation = vars.map {
        case (k, xf) =>
          val freshErrorVar = getNewErrorVar
          And(Seq(Equals(freshMap(k), Plus(k, freshErrorVar)),
          LessEquals(RationalLiteral(-xf.maxError), freshErrorVar),
          LessEquals(freshErrorVar, RationalLiteral(xf.maxError))))
        }
        //println("\ncorrelation cond:  " + And(correlation.toSeq))
      
      val xfc = realRange.get.config
      //val newConfig = xfc
      val newConfig = xfc.addCondition(And(correlation.toSeq)) 
        //new XFloatConfig(xfc.reporter, xfc.solver, BooleanLiteral(true), xfc.precision, xfc.machineEps, xfc.solverMaxIter,
        //xfc.solverPrecision, xfc.additionalConstraints ++ correlation.toSeq)

      val realRangeWithCorrelation = new XFloat(realRange.get.tree, realRange.get.approxInterval,
        realRange.get.error, newConfig)
      //println("\n" + realRangeWithCorrelation.config.getCondition)


      solver.clearCounts
      val diff = (floatRange.get - removeErrors(realRangeWithCorrelation)).interval
      reporter.info("STATS for diff: " + solver.getCounts)

      val maxError = max(abs(diff.xlo), abs(diff.xhi))
      maxError
    } else {
      println("Other path not feasible")
      Rational.zero
    }
  }*/

  /*private def evalErrorExpr(expr: Expr, vars: Map[Expr, XFloat]): Rational = expr match {
    case InitialNoise(v @ Variable(_)) => vars(v).maxError
    case RationalLiteral(v) => v
    case IntLiteral(v) => Rational(v)
    case UMinus(rhs) => - evalErrorExpr(rhs, vars)
    case Plus(lhs, rhs) => evalErrorExpr(lhs, vars) + evalErrorExpr(rhs, vars)
    case Minus(lhs, rhs) => evalErrorExpr(lhs, vars) - evalErrorExpr(rhs, vars)
    case Times(lhs, rhs) => evalErrorExpr(lhs, vars) * evalErrorExpr(rhs, vars)
    case Division(lhs, rhs) => evalErrorExpr(lhs, vars) / evalErrorExpr(rhs, vars)
    case Sqrt(t) => affine.Utils.sqrtUp(evalErrorExpr(t, vars))
  }*/

  /*private def getDiffPathsConditions(cond: Expr, inputs: Map[Expr, XFloat], config: XFloatConfig): (Expr, Expr) = cond match {
    case LessThan(l, r) =>
      val errLeft = eval(l, inputs, config).maxError
      val errRight = eval(r, inputs, config).maxError
      val floatCond = LessThan(l, Plus(r, RationalLiteral(errLeft + errRight)))
      val realCond = GreaterEquals(l, Minus(r, RationalLiteral(errLeft + errRight)))
      (floatCond, realCond)

    case LessEquals(l, r) =>
      val errLeft = eval(l, inputs, config).maxError
      val errRight = eval(r, inputs, config).maxError
      val floatCond = LessEquals(l, Plus(r, RationalLiteral(errLeft + errRight)))
      val realCond = GreaterThan(l, Minus(r, RationalLiteral(errLeft + errRight)))
      (floatCond, realCond)

    case GreaterThan(l, r) =>
      val errLeft = eval(l, inputs, config).maxError
      val errRight = eval(r, inputs, config).maxError
      val floatCond = GreaterThan(l, Minus(r, RationalLiteral(errLeft + errRight)))
      val realCond = LessEquals(l, Plus(r, RationalLiteral(errLeft + errRight)))
      (floatCond, realCond)

    case GreaterEquals(l, r) =>
      val errLeft = eval(l, inputs, config).maxError
      val errRight = eval(r, inputs, config).maxError
      val floatCond = GreaterEquals(l, Minus(r, RationalLiteral(errLeft + errRight)))
      val realCond = LessThan(l, Plus(r, RationalLiteral(errLeft + errRight)))
      (floatCond, realCond)
  }*/

  /*private def addConditionToInputs(inputs: Map[Expr, XFloat], cond: Expr): Map[Expr, XFloat] = {
    inputs.map{
      case (k, x) =>
       (k, new XFloat(x.tree, x.approxInterval, x.error, x.config.addCondition(cond)))
    }
  }

  private def addConditionToInputsAndRemoveErrors(inputs: Map[Expr, XFloat], cond: Expr): Map[Expr, XFloat] = {
    inputs.map{
      case (k, x) =>
       (k, new XFloat(x.tree, x.approxInterval, new XRationalForm(Rational.zero),
        x.config.addCondition(cond).updatePrecision(solverMaxIterHigh, solverPrecisionHigh)))
    }
  }

  private def getFreshMap(vars: Set[Expr]): Map[Expr, Expr] = {
    vars.collect {
      case v @ Variable(id) => (v, getFreshVarOf(id.toString))
    }.toMap
  }

  private def freshenUp(expr: Expr, freshMap: Map[Expr, Expr], inputs: Map[Expr, XFloat]): (Expr, Map[Expr, XFloat]) = {
    val freshExpr = replace(freshMap, expr)
    val freshInputs: Map[Expr, XFloat] = inputs.collect {
      case (k, xf) if(freshMap.contains(k)) =>
        val newXf = new XFloat(replace(freshMap, xf.tree), xf.approxInterval, xf.error, xf.config.freshenUp(freshMap))
       (freshMap(k), newXf)
    }
    (freshExpr, freshInputs)
  }*/

  /*
  private def mergeXFloatWithExtraError(one: Option[XFloat], two: Option[XFloat], config: XFloatConfig,
    pathError: Rational): Option[XFloat] = (one, two) match {
    case (Some(x1), Some(x2)) =>
      val newInt = x1.realInterval.union(x2.realInterval)
      val newError = max(max(x1.maxError, x2.maxError), pathError)
      val fresh = getNewXFloatVar
      val newConfig = config.addCondition(rangeConstraint(fresh, newInt))
      Some(xFloatWithUncertain(fresh, newInt, newConfig, newError, false)._1)
    case (Some(x1), None) =>
      if (pathError != zero) {
        val newError = max(x1.maxError, pathError)
        val newInt = x1.realInterval
        val fresh = getNewXFloatVar
        val newConfig = config.addCondition(rangeConstraint(fresh, newInt))
        Some(xFloatWithUncertain(fresh, newInt, newConfig, newError, false)._1)
      } else
        Some(x1)
    case (None, Some(x2)) =>
      if (pathError != zero) {
        val newError = max(x2.maxError, pathError)
        val newInt = x2.realInterval
        val fresh = getNewXFloatVar
        val newConfig = config.addCondition(rangeConstraint(fresh, newInt))
        Some(xFloatWithUncertain(fresh, newInt, newConfig, newError, false)._1)
      } else
        Some(x2)
    case (None, None) => None
  }

  private def mergeXFloat(one: Option[XFloat], two: Option[XFloat], config: XFloatConfig): Option[XFloat] = (one, two) match {
    case (Some(x1), Some(x2)) =>
      val newInt = x1.realInterval.union(x2.realInterval)
      val newError = max(x1.maxError, x2.maxError)
      val fresh = getNewXFloatVar
      val newConfig = config.addCondition(rangeConstraint(fresh, newInt))
      Some(xFloatWithUncertain(fresh, newInt, newConfig, newError, false)._1)
    case (Some(x1), None) => Some(x1)
    case (None, Some(x2)) => Some(x2)
    case (None, None) => None
  }
  */
  /*private def compactXFloat(xfloat: XFloat, newTree: Expr): XFloat = {
    val newConfig = xfloat.config.addCondition(rangeConstraint(newTree, xfloat.realInterval))
    val (newXFloat, index) = xFloatWithUncertain(newTree, xfloat.realInterval, newConfig, xfloat.maxError, false)
    newXFloat
  }*/

  /*
  private def removeErrors(xf: XFloat): XFloat = {
    new XFloat(xf.tree, xf.approxInterval, new XRationalForm(Rational.zero), xf.config)
  }

  private def rangeConstraint(v: Expr, i: RationalInterval): Expr = {
    And(LessEquals(RationalLiteral(i.xlo), v), LessEquals(v, RationalLiteral(i.xhi)))
  }

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
