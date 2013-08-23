/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import purescala.Definitions._

import ceres.common.{Interval, EmptyInterval, NormalInterval}

import real.Trees._
import Precision._

class Simulator(reporter: Reporter) {

  val simSize = 10//000000//00
  reporter.info("Simulation size: " + simSize + "\n")

  def simulateThis(vc: VerificationCondition, precision: Precision) = {
    reporter.info("-----> Simulating function " + vc.funDef.id.name + "...")
    val funDef = vc.funDef

    val body = vc.body

    val inputs: Map[Variable, (RationalInterval, Rational)] = inputs2intervals(vc.variables)
    println("Inputs: " + inputs)

    val (maxRoundoff, resInterval) = precision match {
      case Float32 => runFloatSimulation(inputs, body)
      case Float64 => runDoubleSimulation(inputs, body)
    }
    //val (maxRoundoff, resInterval) = (0.0, Interval(0.0) )

    val intInputs: Map[Expr, RationalInterval] = inputs.map( x => (x._1 -> RationalInterval(x._2._1.xlo, x._2._1.xhi) ))
    val xratInputs: Map[Expr, XRationalForm] = inputs.map ( x => (x._1 -> XRationalForm(x._2._1) ) )

    //vc.affineRange = Some(evaluateXRationalForm(body, xratInputs).interval)
    reporter.info("Interval range: " + evaluateInterval(body, intInputs))
    //reporter.info("Affine range:   " + evaluateXRationalForm(body, xratInputs).interval)
    reporter.info("Simulated interval: " + resInterval)
    reporter.info("Max error: " + maxRoundoff)
  }

  private def runDoubleSimulation(inputs: Map[Variable, (RationalInterval, Rational)], body: Expr): (Double, Interval) = {
    val r = new scala.util.Random(System.currentTimeMillis)
    var counter = 0
    var resInterval: Interval = EmptyInterval
    var maxRoundoff: Double = 0.0

    while(counter < simSize) {
      var randomInputs = new collection.immutable.HashMap[Expr, (Double, Rational)]()

      for ((k, ((i, n))) <- inputs) {
        val ideal = i.xlo + Rational(r.nextDouble) * (i.xhi - i.xlo)
        val actual: Rational =
          if (n == Rational.zero) ideal // only roundoff
          else if (r.nextBoolean) ideal - Rational(r.nextDouble) * n
          else ideal + Rational(r.nextDouble) * n

        assert(Rational.abs(ideal - actual) <= n)
        randomInputs += ((k, (actual.toDouble, ideal)))
      }
      try {
        val (resDouble, resRat) = evaluate(body, randomInputs)
        maxRoundoff = math.max(maxRoundoff, math.abs(resDouble - resRat.toDouble))
        resInterval = extendInterval(resInterval, resDouble)
      } catch {
        case e: Exception =>;
        case _: Throwable =>;
      }
      counter += 1
    }
    (maxRoundoff, resInterval)
  }

  private def runFloatSimulation(inputs: Map[Variable, (RationalInterval, Rational)], body: Expr): (Double, Interval) = {
    val r = new scala.util.Random(System.currentTimeMillis)
    var counter = 0
    var resInterval: Interval = EmptyInterval
    var maxRoundoff: Double = 0.0

    while(counter < simSize) {
      var randomInputs = new collection.immutable.HashMap[Expr, (Float, Rational)]()

      for ((k, ((i, n))) <- inputs) {
        val ideal = i.xlo + Rational(r.nextDouble) * (i.xhi - i.xlo)
        val actual: Rational =
          if (n == Rational.zero) ideal // only roundoff
          else if (r.nextBoolean) ideal - Rational(r.nextDouble) * n
          else ideal + Rational(r.nextDouble) * n

        assert(Rational.abs(ideal - actual) <= n)
        randomInputs += ((k, (actual.toFloat, ideal)))
      }
      try {
        val (resDouble, resRat) = evaluateSingle(body, randomInputs)
        maxRoundoff = math.max(maxRoundoff, math.abs(resDouble - resRat.toDouble))
        resInterval = extendInterval(resInterval, resDouble)
      } catch {
        case e: Exception =>;
        case _: Throwable => ;
      }
      counter += 1
    }
    (maxRoundoff, resInterval)
  }

  // Returns the double value and range of the ResultVariable
  private def evaluate(expr: Expr, vars: Map[Expr, (Double, Rational)]): (Double, Rational) = {
    val exprs: Seq[Expr] = expr match {
      case And(args) => args
      case _ => Seq(expr)
    }
    var currentVars: Map[Expr, (Double, Rational)] = vars
    for (e <- exprs) e match {
      case Equals(variable, value) => currentVars = currentVars + (variable -> eval(value, currentVars))
      case BooleanLiteral(true) => ;
      case _ => reporter.error("Simulation cannot handle: " + expr)
    }
    currentVars(ResultVariable())
  }

  private def evaluateSingle(expr: Expr, vars: Map[Expr, (Float, Rational)]): (Float, Rational) = {
    val exprs: Seq[Expr] = expr match {
      case And(args) => args
      case _ => Seq(expr)
    }
    var currentVars: Map[Expr, (Float, Rational)] = vars
    for (e <- exprs) e match {
      case Equals(variable, value) => currentVars = currentVars + (variable -> evalSingle(value, currentVars))
      case BooleanLiteral(true) => ;
      case _ => reporter.error("Simulation cannot handle: " + expr)
    }
    currentVars(ResultVariable())
  }

  private def evaluateInterval(expr: Expr, vars: Map[Expr, RationalInterval]): RationalInterval = {
    val exprs: Seq[Expr] = expr match {
      case And(args) => args
      case _ => Seq(expr)
    }
    var currentVars: Map[Expr, RationalInterval] = vars
    for (e <- exprs) e match {
      case Equals(variable, value) => currentVars = currentVars + (variable -> evalInterval(value, currentVars))
      case BooleanLiteral(true) => ;
      case _ => reporter.error("Simulation cannot handle: " + expr)
    }
    currentVars(ResultVariable())
  }

  // Run with QuadDouble so that it works also with sqrt and later with sine etc.
  private def evaluateXRationalForm(expr: Expr, vars: Map[Expr, XRationalForm]): XRationalForm = {
    val exprs: Seq[Expr] = expr match {
      case And(args) => args
      case _ => Seq(expr)
    }
    var currentVars: Map[Expr, XRationalForm] = vars
    for (e <- exprs) e match {
      case Equals(variable, value) => currentVars = currentVars + (variable -> evalXRationalForm(value, currentVars))
      case BooleanLiteral(true) => ;
      case _ => reporter.error("Simulation cannot handle: " + expr)
    }
    currentVars(ResultVariable())
  }

  private def eval(tree: Expr, vars: Map[Expr, (Double, Rational)]): (Double, Rational) = tree match {
    case v @ Variable(id) =>  vars(v)
    case RationalLiteral(v) => (v.toDouble, v)
    //case IntLiteral(v) => (v.toDouble, Rational(v))
    case UMinusR(e) =>
      val (eDbl, eRat) = eval(e, vars)
      (-eDbl, -eRat)
    case PlusR(lhs, rhs) =>
      val (lhsDbl, lhsRat) = eval(lhs, vars)
      val (rhsDbl, rhsRat) = eval(rhs, vars)
      (lhsDbl + rhsDbl, lhsRat + rhsRat)
    case MinusR(lhs, rhs) =>
      val (lhsDbl, lhsRat) = eval(lhs, vars)
      val (rhsDbl, rhsRat) = eval(rhs, vars)
      (lhsDbl - rhsDbl, lhsRat - rhsRat)
    case TimesR(lhs, rhs) =>
      val (lhsDbl, lhsRat) = eval(lhs, vars)
      val (rhsDbl, rhsRat) = eval(rhs, vars)
      (lhsDbl * rhsDbl, lhsRat * rhsRat)
    case DivisionR(lhs, rhs) =>
      val (lhsDbl, lhsRat) = eval(lhs, vars)
      val (rhsDbl, rhsRat) = eval(rhs, vars)
      (lhsDbl / rhsDbl, lhsRat / rhsRat)

    case SqrtR(e) =>
      val (eDbl, eRat) = eval(e, vars)
      (math.sqrt(eDbl), Rational(math.sqrt(eRat.toDouble)))

    case _ =>
      throw UnsupportedRealFragmentException("Can't handle: " + tree.getClass)
      (Double.NaN, Rational(0))
  }

  private def evalSingle(tree: Expr, vars: Map[Expr, (Float, Rational)]): (Float, Rational) = tree match {
    case v @ Variable(id) =>  vars(v)
    case RationalLiteral(v) => (v.toFloat, v)
    //case IntLiteral(v) => (v.toFloat, Rational(v))
    case UMinusR(e) =>
      val (eDbl, eRat) = evalSingle(e, vars)
      (-eDbl, -eRat)
    case PlusR(lhs, rhs) =>
      val (lhsDbl, lhsRat) = evalSingle(lhs, vars)
      val (rhsDbl, rhsRat) = evalSingle(rhs, vars)
      (lhsDbl + rhsDbl, lhsRat + rhsRat)
    case MinusR(lhs, rhs) =>
      val (lhsDbl, lhsRat) = evalSingle(lhs, vars)
      val (rhsDbl, rhsRat) = evalSingle(rhs, vars)
      (lhsDbl - rhsDbl, lhsRat - rhsRat)
    case TimesR(lhs, rhs) =>
      val (lhsDbl, lhsRat) = evalSingle(lhs, vars)
      val (rhsDbl, rhsRat) = evalSingle(rhs, vars)
      (lhsDbl * rhsDbl, lhsRat * rhsRat)
    case DivisionR(lhs, rhs) =>
      val (lhsDbl, lhsRat) = evalSingle(lhs, vars)
      val (rhsDbl, rhsRat) = evalSingle(rhs, vars)
      (lhsDbl / rhsDbl, lhsRat / rhsRat)

    case _ =>
      throw UnsupportedRealFragmentException("Can't handle: " + tree.getClass)
      (Float.NaN, Rational(0))
  }

  private def evalInterval(tree: Expr, vars: Map[Expr, RationalInterval]): RationalInterval = tree match {
    case v @ Variable(id) => vars(v)
    case RationalLiteral(v) => RationalInterval(v, v)
    //case IntLiteral(v) => RationalInterval(Rational(v), Rational(v))
    case UMinusR(e) => - evalInterval(e, vars)
    case PlusR(lhs, rhs) => evalInterval(lhs, vars) + evalInterval(rhs, vars)
    case MinusR(lhs, rhs) => evalInterval(lhs, vars) - evalInterval(rhs, vars)
    case TimesR(lhs, rhs) => evalInterval(lhs, vars) * evalInterval(rhs, vars)
    case DivisionR(lhs, rhs) => evalInterval(lhs, vars) / evalInterval(rhs, vars)
    case _ =>
      throw UnsupportedRealFragmentException("Can't handle: " + tree.getClass)
      null
  }

  private def evalXRationalForm(tree: Expr, vars: Map[Expr, XRationalForm]): XRationalForm = tree match {
    case v @ Variable(id) => vars(v)
    case RationalLiteral(v) => new XRationalForm(v)
    //case IntLiteral(v) => new XRationalForm(Rational(v))
    case UMinusR(e) => - evalXRationalForm(e, vars)
    case PlusR(lhs, rhs) => evalXRationalForm(lhs, vars) + evalXRationalForm(rhs, vars)
    case MinusR(lhs, rhs) => evalXRationalForm(lhs, vars) - evalXRationalForm(rhs, vars)
    case TimesR(lhs, rhs) => evalXRationalForm(lhs, vars) * evalXRationalForm(rhs, vars)
    case DivisionR(lhs, rhs) => evalXRationalForm(lhs, vars) / evalXRationalForm(rhs, vars)
    case _ =>
      throw UnsupportedRealFragmentException("Can't handle: " + tree.getClass)
      null
    }

  private def extendInterval(i: Interval, d: Double): Interval = i match {
    case EmptyInterval => Interval(d)
    case NormalInterval(xlo, xhi) =>
      if (d >= xlo && d <= xhi) i
      else if (d <= xlo) NormalInterval(d, xhi)
      else if (d >= xhi) NormalInterval(xlo, d)
      else null
  }

  private def inputs2intervals(vars: VariablePool): Map[Variable, (RationalInterval, Rational)] = {
    var variableMap: Map[Variable, (RationalInterval, Rational)] = Map.empty

    for(rec <- vars.getValidRecords) {
      rec match {
        case Record(v @ Variable(_), a @ Variable(_), Some(lo), Some(up), Some(unc)) =>
          val interval = RationalInterval(lo, up)
          variableMap = variableMap + (v -> (interval, unc))

        case Record(v @ Variable(_), a @ Variable(_), Some(lo), Some(up), None) =>
          val interval = RationalInterval(lo, up)
          variableMap = variableMap + (v -> (interval, Rational.zero))
      }
    }
    variableMap
  }


}