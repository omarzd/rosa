package leon
package numerics

import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Definitions._
import purescala.Common._

import affine._
import affine.XFloat._
import Rational.zero

import RoundoffType._
import Precision._
//import Utils._
import VariableShop._

class XEvaluator(reporter: Reporter, solver: NumericSolver, precision: Precision, vcMap: Map[FunDef, VerificationCondition]) {
  val printStats = true
  val unitRoundoff = getUnitRoundoff(precision)
  val unitRoundoffDefault = getUnitRoundoff(Float64)


  def evaluateWithFncCalls(expr: List[Expr], precondition: Expr, inputs: Map[Variable, Record]): (Map[Expr, XFloat], Map[Int, Expr]) = {
    println("Evaluating: " + expr)
    val config = XFloatConfig(reporter, solver, precondition, precision, unitRoundoff)
    val (variables, indices) = variables2xfloats(inputs, config)
    solver.clearCounts
    val values = inXFloatsWithFncs(expr, variables, config) -- inputs.keys
    if (printStats) reporter.info("STAAATS: " + solver.getCounts)
    (values, indices)
  }

  private def inXFloatsWithFncs(exprs: List[Expr], vars: Map[Expr, XFloat], config: XFloatConfig): Map[Expr, XFloat] = {
    var currentVars: Map[Expr, XFloat] = vars

    for (expr <- exprs) expr match {
      case Equals(variable, value) =>
        try {
          val computedValue = evalWithFncs(value, currentVars, config)
          currentVars = currentVars + (variable -> computedValue)
          //println("Computed for: " + variable + "  : " + computedValue)
          //println("tree: " + computedValue.tree)
        } catch {
          case UnsupportedFragmentException(msg) => reporter.error(msg)
        }

      case BooleanLiteral(true) => ;
      case _ =>
        reporter.error("AA cannot handle: " + expr)
    }

    currentVars
  }

  private def evalWithFncs(expr: Expr, vars: Map[Expr, XFloat], config: XFloatConfig): XFloat = expr match {
    case v @ Variable(id) => vars(v)
    case RationalLiteral(v) => XFloat(v, config)
    case IntLiteral(v) => XFloat(v, config)
    case UMinus(rhs) => - evalWithFncs(rhs, vars, config)
    case Plus(lhs, rhs) => evalWithFncs(lhs, vars, config) + evalWithFncs(rhs, vars, config)
    case Minus(lhs, rhs) => evalWithFncs(lhs, vars, config) - evalWithFncs(rhs, vars, config)
    case Times(lhs, rhs) => evalWithFncs(lhs, vars, config) * evalWithFncs(rhs, vars, config)
    case Division(lhs, rhs) => evalWithFncs(lhs, vars, config) / evalWithFncs(rhs, vars, config)
    case Sqrt(t) => evalWithFncs(t, vars, config).squareRoot

    case FunctionInvocation(funDef, args) =>
      //println("function call: " + funDef.id.toString)
      val fresh = getNewFncVariable(funDef.id.name)
      val arguments: Map[Expr, Expr] = funDef.args.map(decl => decl.toVariable).zip(args).toMap
      val newBody = replace(arguments, vcMap(funDef).body)
      println("newBody: " + newBody)
      println("inputs: ")
      for((k, v) <- vars) {
        println(k + ": " +v.tree)
        println("compacted: " + compactXFloat(v, k).tree)
      }
      val bodyAsList = newBody match {
        case And(list) => list
        case eq: Equals => List(eq)
        // e.g. if the function has if-then-else's
        case _=> throw UnsupportedFragmentException("AA cannot handle: " + expr); null
      }

      println("bodyList: " + bodyAsList)
      val vals = inXFloatsWithFncs(bodyAsList.toList, vars, config)
      val result = vals(ResultVariable())
      println("result: " + result)
      val newXFloat = compactXFloat(result, fresh)
      println("newXFloat: " + newXFloat)
      newXFloat
      
    case _ =>
      throw UnsupportedFragmentException("AA cannot handle: " + expr)
      null
  }

  private def compactXFloat(xfloat: XFloat, newTree: Expr): XFloat = {
    val newConfig = xfloat.config.addCondition(rangeConstraint(newTree, xfloat.realInterval))
    val (newXFloat, index) = xFloatWithUncertain(newTree, xfloat.realInterval, newConfig, xfloat.maxError, false)
    newXFloat
  }

  private def rangeConstraint(v: Expr, i: RationalInterval): Expr = {
    And(LessEquals(RationalLiteral(i.xlo), v), LessEquals(v, RationalLiteral(i.xhi)))
  }

  def evaluate(expr: List[Expr], precondition: Expr, inputs: Map[Variable, Record]): (Map[Expr, XFloat], Map[Int, Expr]) = {
    val config = XFloatConfig(reporter, solver, precondition, precision, unitRoundoff)
    val (variables, indices) = variables2xfloats(inputs, config)
    solver.clearCounts
    val values = inXFloats(reporter, expr, variables, config) -- inputs.keys
    if (printStats) reporter.info("STAAATS: " + solver.getCounts)
    (values, indices)
  }


   // Returns a map from all variables to their final value, including local vars
  private def inXFloats(reporter: Reporter, exprs: List[Expr], vars: Map[Expr, XFloat], config: XFloatConfig): Map[Expr, XFloat] = {
    var currentVars: Map[Expr, XFloat] = vars

    for (expr <- exprs) expr match {
      case Equals(variable, value) =>
        try {
          val computedValue = eval(value, currentVars, config)
          currentVars = currentVars + (variable -> computedValue)
        } catch {
          case UnsupportedFragmentException(msg) => reporter.error(msg)
        }

      case BooleanLiteral(true) => ;
      case _ =>
        reporter.error("AA cannot handle: " + expr)
    }

    currentVars
  }

  // Evaluates an arithmetic expression
  private def eval(expr: Expr, vars: Map[Expr, XFloat], config: XFloatConfig): XFloat = expr match {
    case v @ Variable(id) => vars(v)
    case RationalLiteral(v) => XFloat(v, config)
    case IntLiteral(v) => XFloat(v, config)
    case UMinus(rhs) => - eval(rhs, vars, config)
    case Plus(lhs, rhs) => eval(lhs, vars, config) + eval(rhs, vars, config)
    case Minus(lhs, rhs) => eval(lhs, vars, config) - eval(rhs, vars, config)
    case Times(lhs, rhs) => eval(lhs, vars, config) * eval(rhs, vars, config)
    case Division(lhs, rhs) => eval(lhs, vars, config) / eval(rhs, vars, config)
    case Sqrt(t) => eval(t, vars, config).squareRoot
    case _ =>
      throw UnsupportedFragmentException("AA cannot handle: " + expr)
      null
  }
}