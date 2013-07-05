package leon
package numerics

import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Definitions._
import purescala.Common._

import affine._
import affine.XFloat._
import Rational.{zero, max, abs}

import RoundoffType._
import Precision._
import VariableShop._

class XEvaluator(reporter: Reporter, solver: NumericSolver, precision: Precision, vcMap: Map[FunDef, VerificationCondition]) {
  val printStats = true
  val unitRoundoff = getUnitRoundoff(precision)
  val unitRoundoffDefault = getUnitRoundoff(Float64)
  val compactingThreshold = 100


  def evaluate(expr: Expr, precondition: Expr, inputs: Map[Variable, Record]): (Map[Expr, XFloat], Map[Int, Expr]) = {
    val config = XFloatConfig(reporter, solver, precondition, precision, unitRoundoff, solverMaxIterMedium, solverPrecisionMedium)
    val (variables, indices) = variables2xfloats(inputs, config)
    solver.clearCounts
    val values = inXFloats(reporter, expr, variables, config)._1 -- inputs.keys
    if (printStats) reporter.info("STAAATS: " + solver.getCounts)
    (values, indices)
  }

  private def inXFloats(reporter: Reporter, expr: Expr, vars: Map[Expr, XFloat],
    config: XFloatConfig): (Map[Expr, XFloat], Option[XFloat]) = {
    expr match {
      case And(args) =>
        var currentVars: Map[Expr, XFloat] = vars
        for (arg <- args) {
          val (map, xf) = inXFloats(reporter, arg, currentVars, config)
          currentVars = map
        }
        (currentVars, None)

      case Equals(variable, IfExpr(cond, then, elze)) =>
        // Errors and ranges from the two branches
        val thenConfig = config.addCondition(cond)
        val elzeConfig = config.addCondition(negate(cond))
        val (thenMap, thenValue) =
          if (sanityCheck(thenConfig.getCondition))
            inXFloats(reporter, then, addConditionToInputs(vars, cond), thenConfig)
          else (vars, None)
        val (elzeMap, elzeValue) =
          if (sanityCheck(elzeConfig.getCondition))
            inXFloats(reporter, elze, addConditionToInputs(vars, negate(cond)), elzeConfig)
          else (vars, None)
        assert(!thenValue.isEmpty || !elzeValue.isEmpty)
        println("thenValue: " + thenValue)
        println("elseValue: " + elzeValue)
        // When the actual computation goes a different way than the real one
        val (flCond1, reCond1) = getDiffPathsConditions(cond, vars, config)
        val (flCond2, reCond2) = getDiffPathsConditions(negate(cond), vars, config)
        //println("flCond1: " + flCond1); println("reCond1: " + reCond1); println("flCond2: " + flCond2);  println("reCond2: " + reCond2)

        // TODO: for this we have to set the solver precision high!
        val pathErrorThen =
          getPathError(elze, And(flCond1, negate(cond)), then, And(cond, reCond1), vars, config)
        println("pathError1: %.16g".format(pathErrorThen.toDouble))

        val pathErrorElze =
          getPathError(then, And(flCond2, cond), elze, And(negate(cond), reCond2), vars, config)
        println("pathError2: %.16g".format(pathErrorElze.toDouble))
        // TODO: do we  also have to keep track of the flRange computed? I think so

        // TODO The merging has to remove the conditions again!
        (vars + (variable -> mergeXFloatWithExtraError(thenValue, elzeValue, config, max(pathErrorThen, pathErrorElze)).get), None)
      
      case IfExpr(cond, then, elze) =>
        // TODO: eval error across paths
        val thenConfig = config.addCondition(cond)
        val elzeConfig = config.addCondition(Not(cond))
        
        val (thenMap, thenValue) =
          if (sanityCheck(thenConfig.getCondition))
            inXFloats(reporter, then, addConditionToInputs(vars, cond), thenConfig)
          else (vars, None)

        val (elzeMap, elzeValue) =
          if (sanityCheck(elzeConfig.getCondition))
            inXFloats(reporter, elze, addConditionToInputs(vars, negate(cond)), elzeConfig)
          else (vars, None)
        assert(thenValue.isEmpty && elzeValue.isEmpty)
        
        val (flCond1, reCond1) = getDiffPathsConditions(cond, vars, config)
        val (flCond2, reCond2) = getDiffPathsConditions(negate(cond), vars, config)
        val pathErrorThen = getPathErrorForRes(elze, And(flCond1, negate(cond)), then, And(cond, reCond1), vars, config)
        println("pathError1: %.16g".format(pathErrorThen.toDouble))

        val pathErrorElze = getPathErrorForRes(then, And(flCond2, cond), elze, And(negate(cond), reCond2), vars, config)
        println("pathError2: %.16g".format(pathErrorElze.toDouble))

        mergeXFloatWithExtraError(thenMap.get(ResultVariable()), elzeMap.get(ResultVariable()), config,
          max(pathErrorThen, pathErrorElze)) match {
          case Some(res) => (vars + (ResultVariable() -> res), None)
          case None => (vars, None)
        }

      case Equals(variable, value) =>
        val computedValue = eval(value, vars, config)
        (vars + (variable -> computedValue), None)

      case Variable(_) | RationalLiteral(_) | IntLiteral(_) | UMinus(_) | Plus(_, _) | Minus(_, _) | Times(_, _) | Division(_, _) | Sqrt(_) =>
        (vars, Some(eval(expr, vars, config)))

      case BooleanLiteral(true) => (vars, None)
      case _ =>
        reporter.error("AA cannot handle: " + expr)
        (Map.empty, None)
    }
  }

  // The conditions are not fresh, we do that here automatically
  // TODO: this has a bug with function calls
  private def getPathError(flExpr: Expr, flCond: Expr, reExpr: Expr, reCond: Expr, vars: Map[Expr, XFloat],
    config: XFloatConfig): Rational = {
    //val flCond = And(flCond1, negate(cond))
    if (sanityCheck(flCond)) {
      // execution taken by actual computation
      val flConfig = config.addCondition(flCond).updatePrecision(solverMaxIterHigh, solverPrecisionHigh)
      val flVars = addConditionToInputsAndRemoveErrors(vars, flCond)
      //println("fl vars:"); flVars.foreach {f => println(f); println(f._2.config.solverMaxIter)}
      val (m, floatRange) = inXFloats(reporter, flExpr, flVars, flConfig)
      //println("floatRange: " + floatRange)
            
      val freshMap = getFreshMap(vars.keySet)
      val (freshThen, freshVars) = freshenUp(reExpr, freshMap, vars)
      val reConfig = config.addCondition(reCond).freshenUp(freshMap).updatePrecision(solverMaxIterHigh, solverPrecisionHigh)
      val reVars = addConditionToInputsAndRemoveErrors(freshVars, replace(freshMap, reCond))
      //println("re vars:"); reVars.foreach {f => println(f); println(f._2.config.getCondition)}
      val (mm, realRange) = inXFloats(reporter, freshThen, reVars, reConfig)
      //println("realRange: "+ removeErrors(realRange.get))
      
      val diff = (floatRange.get - removeErrors(realRange.get)).interval
      val maxError = max(abs(diff.xlo), abs(diff.xhi))
      maxError
    } else {
      Rational.zero
    }
  }

  // TODO: this has a bug with function calls
  private def getPathErrorForRes(flExpr: Expr, flCond: Expr, reExpr: Expr, reCond: Expr, vars: Map[Expr, XFloat],
    config: XFloatConfig): Rational = {
    //val flCond = And(flCond1, negate(cond))
    if (sanityCheck(flCond)) {
      // execution taken by actual computation
      val flConfig = config.addCondition(flCond)
      val flVars = addConditionToInputsAndRemoveErrors(vars, flCond)
      //println("fl vars:"); flVars.foreach {f => println(f); println(f._2.config.getCondition)}
      val (flMap, _) = inXFloats(reporter, flExpr, flVars, flConfig)
      val floatRange = flMap.get(ResultVariable())
      println("floatRange: " + floatRange)
            
      val freshMap = getFreshMap(vars.keySet)
      val (freshThen, freshVars) = freshenUp(reExpr, freshMap, vars)
      val reConfig = config.addCondition(reCond).freshenUp(freshMap)
      val reVars = addConditionToInputsAndRemoveErrors(freshVars, replace(freshMap, reCond))
      //println("re vars:"); reVars.foreach {f => println(f); println(f._2.config.getCondition)}
      val (reMap, _) = inXFloats(reporter, freshThen, reVars, reConfig)
      val realRange = removeErrors(reMap.get(ResultVariable()).get)
      println("realRange: "+ realRange)
      
      val diff = (floatRange.get - realRange).interval
      val maxError = max(abs(diff.xlo), abs(diff.xhi))
      maxError
    } else {
      Rational.zero
    }

  }

  
  // Evaluates an arithmetic expression
  private def eval(expr: Expr, vars: Map[Expr, XFloat], config: XFloatConfig): XFloat = {
    val xfloat = expr match {
    case v @ Variable(id) => vars(v)
    case RationalLiteral(v) => XFloat(v, config)
    case IntLiteral(v) => XFloat(v, config)
    case UMinus(rhs) => - eval(rhs, vars, config)
    case Plus(lhs, rhs) => eval(lhs, vars, config) + eval(rhs, vars, config)
    case Minus(lhs, rhs) => eval(lhs, vars, config) - eval(rhs, vars, config)
    case Times(lhs, rhs) => eval(lhs, vars, config) * eval(rhs, vars, config)
    case Division(lhs, rhs) => eval(lhs, vars, config) / eval(rhs, vars, config)
    case Sqrt(t) => eval(t, vars, config).squareRoot
    case FunctionInvocation(funDef, args) =>
      // EValuate the function, i.e. compute the postcondition and inline it
      println("function call: " + funDef.id.toString)
      val fresh = getNewFncVariable(funDef.id.name)
      val arguments: Map[Expr, Expr] = funDef.args.map(decl => decl.toVariable).zip(args).toMap
      val newBody = replace(arguments, vcMap(funDef).body)
      /*val bodyAsList = newBody match {
        case And(list) => list
        case eq: Equals => List(eq)
        // e.g. if the function has if-then-else's
        case _=> throw UnsupportedFragmentException("AA cannot handle: " + expr); null
      }*/
      //println("bodyList: " + bodyAsList)
      val vals = inXFloats(reporter, newBody, vars, config)
      val result = vals._1(ResultVariable())
      //println("result: " + result)
      val newXFloat = compactXFloat(result, fresh)
      println("newXFloat: " + newXFloat)
      newXFloat
    case _ =>
      throw UnsupportedFragmentException("AA cannot handle: " + expr)
      null
    }
    if (formulaSize(xfloat.tree) > compactingThreshold) {
      reporter.warning("compacting, size: " + formulaSize(xfloat.tree))
      val fresh = getNewXFloatVar
      compactXFloat(xfloat, fresh)
    } else {
      xfloat
    }
  }

  private def getDiffPathsConditions(cond: Expr, inputs: Map[Expr, XFloat], config: XFloatConfig): (Expr, Expr) = cond match {
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
  }

  private def addConditionToInputs(inputs: Map[Expr, XFloat], cond: Expr): Map[Expr, XFloat] = {
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
  }

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

  private def compactXFloat(xfloat: XFloat, newTree: Expr): XFloat = {
    val newConfig = xfloat.config.addCondition(rangeConstraint(newTree, xfloat.realInterval))
    val (newXFloat, index) = xFloatWithUncertain(newTree, xfloat.realInterval, newConfig, xfloat.maxError, false)
    newXFloat
  }

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
}