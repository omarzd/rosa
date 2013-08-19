/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

import real.Trees._
import real.TreeOps._
import XFloat._

class FloatApproximator(reporter: Reporter, solver: RealSolver, options: RealOptions,
  precondition: Expr, inputs: VariablePool) extends TransformerWithPC {
  type C = Seq[Expr]
  val initC = Nil

  val transformer = new LeonToZ3Transformer(inputs)
    
  val config = XFloatConfig(reporter, solver, transformer.getZ3Expr(precondition, options.defaultPrecision), 
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
    case _ =>
      super.rec(e, path)
  }

    // Evaluates an arithmetic expression
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

  def approximate(e: Expr): Expr = {
    println("finished approximation, xfloats: " + variables)
    this.transform(e)
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