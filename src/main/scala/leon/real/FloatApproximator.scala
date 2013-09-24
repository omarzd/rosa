/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

import real.Trees._
import real.TreeOps._
import XFloat._
import Precision._
import Rational._
import VariableShop._

object FloatApproximator {

  // Just so we have it somewhere, not tested
  def evalWithError(reporter: Reporter, solver: RealSolver, precision: Precision, expr: Expr, precondition: Expr, inputs: VariablePool): Map[Expr, XFloat] = {
    //val config = XFloatConfig(reporter, solver, precondition, options.defaultPrecision, getUnitRoundoff(options.defaultPrecision),
    //  solverMaxIterMedium, solverPrecisionMedium)

    val transformer = new FloatApproximator(reporter, solver, precision, precondition, inputs)
    transformer.transform(expr)

    transformer.variables -- inputs.actualVariables
  }

}

class FloatApproximator(reporter: Reporter, solver: RealSolver, precision: Precision, precondition: Expr, inputs: VariablePool) extends TransformerWithPC {
  type C = Seq[Expr]
  val initC = Nil

  val verboseLocal = false // TODO figure out which verbose that is if we call this 'verbose'

  val leonToZ3 = new LeonToZ3Transformer(inputs)
  val noiseRemover = new NoiseRemover
  val (minVal, maxVal) = precision match { // TODO: alright, this is not exact
    case Float32 => (-Rational(Float.MaxValue), Rational(Float.MaxValue))
    case Float64 => (-Rational(Double.MaxValue), Rational(Double.MaxValue))
    case DoubleDouble => (-Rational(Double.MaxValue), Rational(Double.MaxValue))  // same range as Double
    case QuadDouble => (-Rational(Double.MaxValue), Rational(Double.MaxValue)) // same range as Double
  }
  
  val config = XFloatConfig(solver, leonToZ3.getZ3Expr(noiseRemover.transform(precondition), precision), 
    precision, getUnitRoundoff(precision), solverMaxIterMedium, solverPrecisionMedium)

  if (verboseLocal) println("initial config: " + config)

  var variables: Map[Expr, XFloat] = variables2xfloats(inputs, config)._1

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
    def getXFloat(e: Expr): XFloat = e match {
      case ApproxNode(x) => x
      case FloatLiteral(r, exact) => addCondition(XFloat(r, config), path)
      case v: Variable => addCondition(variables(v), path)
      case And(args) => getXFloat(args.last)
    }

    val newExpr = e match {
      case EqualsF(lhs, rhs) =>
        val x = getXFloat(rec(rhs, path))
        variables = variables + (lhs -> x)
        constraintFromXFloats(Map(lhs -> x))

      case UMinusF(t) => ApproxNode(-getXFloat(rec(t, path)))
      case PlusF(lhs, rhs) =>
        ApproxNode(getXFloat(rec(lhs, path)) + getXFloat(rec(rhs, path)))
      case MinusF(lhs, rhs) =>
        ApproxNode(getXFloat(rec(lhs, path)) - getXFloat(rec(rhs, path)))
      case TimesF(lhs, rhs) =>
        ApproxNode(getXFloat(rec(lhs, path)) * getXFloat(rec(rhs, path)))
      case DivisionF(lhs, rhs) =>
        val r = getXFloat(rec(rhs, path))
        if (possiblyZero(r.interval)) reporter.warning("Potential div-by-zero detected: " + e)
        ApproxNode(getXFloat(rec(lhs, path)) / r)
        
      case SqrtF(t) =>
        val x = getXFloat(rec(t, path))
        if (possiblyNegative(x.interval)) reporter.warning("Potential sqrt of negative detected: " + e)
        ApproxNode(x.squareRoot)    
        
      case FloatIfExpr(cond, den, elze) =>
        val thenBranch =
          if (isFeasible(path :+ cond)) Some(getXFloat(rec(den, register(cond, path))))
          else None

        val elseBranch =
          if (isFeasible(path :+ negate(cond))) Some(getXFloat(rec(elze, register(cond, path))))
          else None
        assert(!thenBranch.isEmpty || !elseBranch.isEmpty)
        
        // TODO: path error
        val pathError = zero
        ApproxNode(mergeXFloatWithExtraError(thenBranch, elseBranch, And(path), pathError))

      case FncValueF(spec) =>
        val (interval, error, constraints) = getResultSpec(spec)
        val fresh = getNewXFloatVar

        val tmp = ApproxNode(xFloatWithUncertain(fresh, interval,
          config.addCondition(replace(Map(ResultVariable() -> fresh), leonToZ3.getZ3Condition(noiseRemover.transform(spec)))),
          error, false)._1)
        tmp

      case FncBodyF(name, body) =>
        val fncValue = rec(body, path)
        ApproxNode(getXFloat(fncValue))

      case _ =>
        super.rec(e, path)
    }
    newExpr match {
      case ApproxNode(x) if (overflowPossible(x.interval)) =>
        reporter.warning("Possible overflow detected at: " + newExpr)
      case _ =>
    }
    newExpr
  }


  
  private def mergeXFloatWithExtraError(one: Option[XFloat], two: Option[XFloat], condition: Expr,
    pathError: Rational): XFloat = (one, two) match {
    case (Some(x1), Some(x2)) =>
      val newInt = x1.realInterval.union(x2.realInterval)
      val newError = max(max(x1.maxError, x2.maxError), pathError)
      val fresh = getNewXFloatVar
      val newConfig = config.addCondition(leonToZ3.getZ3Condition(And(condition, rangeConstraint(fresh, newInt))))
      xFloatWithUncertain(fresh, newInt, newConfig, newError, false)._1
    case (Some(x1), None) =>
      if (pathError != zero) {
        val newError = max(x1.maxError, pathError)
        val newInt = x1.realInterval
        val fresh = getNewXFloatVar
        val newConfig = config.addCondition(leonToZ3.getZ3Condition(And(condition, rangeConstraint(fresh, newInt))))
        xFloatWithUncertain(fresh, newInt, newConfig, newError, false)._1
      } else
        x1
    case (None, Some(x2)) =>
      if (pathError != zero) {
        val newError = max(x2.maxError, pathError)
        val newInt = x2.realInterval
        val fresh = getNewXFloatVar
        val newConfig = config.addCondition(leonToZ3.getZ3Condition(And(condition, rangeConstraint(fresh, newInt))))
        xFloatWithUncertain(fresh, newInt, newConfig, newError, false)._1
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
  
  
 /*if (formulaSize(xfloat.tree) > compactingThreshold) {
    reporter.warning("compacting, size: " + formulaSize(xfloat.tree))
    val fresh = getNewXFloatVar
    compactXFloat(xfloat, fresh)
  } else {
    xfloat
  }*/

  private def constraintFromXFloats(results: Map[Expr, XFloat]): Expr = {
    And(results.foldLeft(Seq[Expr]())(
      (seq, kv) => seq ++ Seq(LessEquals(RealLiteral(kv._2.interval.xlo), kv._1),
                                LessEquals(kv._1, RealLiteral(kv._2.interval.xhi)),
                                Noise(inputs.getIdeal(kv._1), RealLiteral(kv._2.maxError)))))
  }

  private def overflowPossible(interval: RationalInterval): Boolean =
    if (interval.xlo < minVal || maxVal < interval.xhi) true else false
  
  private def possiblyZero(interval: RationalInterval): Boolean =
    if (interval.xlo < Rational.zero && interval.xhi > Rational.zero) true else false

  private def possiblyNegative(interval: RationalInterval): Boolean =
    if (interval.xlo < Rational.zero || interval.xhi < Rational.zero) true else false

  private def addCondition(v: XFloat, cond: Seq[Expr]): XFloat = {
    if (cond.size > 0)
      new XFloat(v.tree, v.approxInterval, v.error, v.config.addCondition(leonToZ3.getZ3Condition(And(cond))))
    else
      v
  }

  private def isFeasible(pre: Seq[Expr]): Boolean = {
    import Sat._
    solver.checkSat(leonToZ3.getZ3Expr(And(pre), precision)) match {
      case (SAT, model) => true
      case (UNSAT, model) => false
      case _ =>
        reporter.info("Sanity check failed! ")// + sanityCondition)
        false
    }
  }
}