/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import purescala.Definitions._
import purescala.Common._

import ceres.common.{Interval, EmptyInterval, NormalInterval}

import real.Trees._
import real.TreeOps._
import real.{FixedPointFormat => FPFormat}
import FPFormat._

/*
 Note: simulation does not work with tuples.
*/
class Simulator(ctx: LeonContext, options: RealOptions, prog: Program, val reporter: Reporter, fncs: Map[FunDef, Fnc]) extends FixedpointCodeGenerator {

  val simSize = 10000000//00
  reporter.info("Simulation size: " + simSize + "\n")

  def simulateThis(vc: VerificationCondition, precision: Precision) = {
    reporter.info("-----> Simulating function " + vc.funDef.id.name + "...")
    val funDef = vc.funDef

    val body = vc.body

    val inputs: Map[Variable, (RationalInterval, Rational)] = inputs2intervals(vc.variables)
    //println("Inputs: " + inputs)

    val (maxRoundoff, resInterval) = precision match {
      case Float32 => runFloatSimulation(inputs, body, vc.variables.resIds.head)
      case Float64 => runDoubleSimulation(inputs, body, vc.variables.resIds.head)
      case FPPrecision(bits) => runFixedpointSimulation(inputs, vc, precision)
      case _=> reporter.warning("Cannot handle this precision: " + precision)
    }
    //val (maxRoundoff, resInterval) = (0.0, Interval(0.0) )

    val intInputs: Map[Expr, RationalInterval] = inputs.map( x => (x._1 -> RationalInterval(x._2._1.xlo, x._2._1.xhi) ))
    val xratInputs: Map[Expr, XRationalForm] = inputs.map ( x => (x._1 -> XRationalForm(x._2._1) ) )

    //vc.affineRange = Some(evaluateXRationalForm(body, xratInputs).interval)
    try {
      reporter.info("Interval range: " + evaluateInterval(vc.variables.resIds.head, body, intInputs))
    } catch {
      case e: Exception => reporter.info("Failed to compute interval due to " + e.getClass)
    }
    //reporter.info("Affine range:   " + evaluateXRationalForm(body, xratInputs).interval)
    reporter.info("Simulated interval: " + resInterval)
    reporter.info("Max error: " + maxRoundoff)
  }

  private def runFixedpointSimulation(inputs: Map[Variable, (RationalInterval, Rational)], vc: VerificationCondition,
    precision: Precision): (Double, Interval) = {
    

    val bitlength = precision.asInstanceOf[FPPrecision].bitlength

    // first generate the comparison code
    val solver = new RangeSolver(options.z3Timeout)
    val (fixedBody, resFracBits) = getFPCode(vc, solver, bitlength, fncs)
    val realBody = vc.body

    // Now do the actual simulation
    val r = new scala.util.Random(System.currentTimeMillis)
    var counter = 0
    var resInterval: Interval = EmptyInterval
    var maxRoundoff: Double = 0.0

    var inputFormats = inputs.map {
      case (v, (interval, error)) => (v -> FPFormat.getFormat(interval.xlo, interval.xhi, bitlength))
    }
    
    while(counter < simSize) {
      var randomInputsRational = new collection.immutable.HashMap[Expr, Rational]()
      var randomInputsFixed = new collection.immutable.HashMap[Expr, Long]()

      for ((k, ((i, n))) <- inputs) {
        val ideal = i.xlo + Rational(r.nextDouble) * (i.xhi - i.xlo)
        val actual: Rational =
          if (n == Rational.zero) ideal // only roundoff
          else if (r.nextBoolean) ideal - Rational(r.nextDouble) * n
          else ideal + Rational(r.nextDouble) * n

        assert(Rational.abs(ideal - actual) <= n)
        randomInputsRational += ((k, ideal))
        randomInputsFixed += ((k, rationalToLong(ideal, inputFormats(k).f)))
      }
      try {
        val resRat = evaluateRational(vc.variables.resIds.head, realBody, randomInputsRational)
        val resFixed = evaluateFixedpoint(vc.variables.resIds.head, fixedBody, randomInputsFixed)
        maxRoundoff = math.max(maxRoundoff, math.abs((longToRational(resFixed, resFracBits) - resRat).toDouble))
        resInterval = extendInterval(resInterval, longToDouble(resFixed, resFracBits))
      } catch {
        case e: Exception =>;
        case _: Throwable =>;
      }
      counter += 1
    }
    (maxRoundoff, resInterval)
  }

  private def runDoubleSimulation(inputs: Map[Variable, (RationalInterval, Rational)], body: Expr, resId: Identifier): (Double, Interval) = {
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
        val (resDouble, resRat) = evaluate(resId, body, randomInputs)
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

  private def runFloatSimulation(inputs: Map[Variable, (RationalInterval, Rational)], body: Expr, resId: Identifier): (Double, Interval) = {
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
        val (resDouble, resRat) = evaluateSingle(resId, body, randomInputs)
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



  private def evaluateFixedpoint(resId: Identifier, expr: Expr, vars: Map[Expr, Long]): Long = {
    val exprs: Seq[Expr] = expr match {
      case And(args) => args
      case _ => Seq(expr)
    }
    var currentVars: Map[Expr, Long] = vars
    for (e <- exprs) e match {
      case Equals(variable, value) => currentVars = currentVars + (variable -> evalFixed(value, currentVars))
      case BooleanLiteral(true) => ;
      case _ => reporter.error("Simulation cannot handle: " + expr)
    }
    currentVars(Variable(resId))
  }

  private def evaluateRational(resId: Identifier, expr: Expr, vars: Map[Expr, Rational]): Rational = {
    val exprs: Seq[Expr] = expr match {
      case And(args) => args
      case _ => Seq(expr)
    }
    var currentVars: Map[Expr, Rational] = vars
    for (e <- exprs) e match {
      case Equals(variable, value) => currentVars = currentVars + (variable -> evalRational(value, currentVars))
      case BooleanLiteral(true) => ;
      case _ => reporter.error("Simulation cannot handle: " + expr)
    }
    currentVars(Variable(resId))
  }

  // Returns the double value and range of the ResultVariable
  private def evaluate(resId: Identifier, expr: Expr, vars: Map[Expr, (Double, Rational)]): (Double, Rational) = {
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
    currentVars(Variable(resId))
  }

  private def evaluateSingle(resId: Identifier, expr: Expr, vars: Map[Expr, (Float, Rational)]): (Float, Rational) = {
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
    currentVars(Variable(resId))
  }

  private def evaluateInterval(resId: Identifier, expr: Expr, vars: Map[Expr, RationalInterval]): RationalInterval = {
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
    currentVars(Variable(resId))
  }

  // Run with QuadDouble so that it works also with sqrt and later with sine etc.
  private def evaluateXRationalForm(resId: Identifier, expr: Expr, vars: Map[Expr, XRationalForm]): XRationalForm = {
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
    currentVars(Variable(resId))
  }

  private def eval(tree: Expr, vars: Map[Expr, (Double, Rational)]): (Double, Rational) = tree match {
    case v @ Variable(id) =>  vars(v)
    case RealLiteral(v) => (v.toDouble, v)
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

  private def evalRational(tree: Expr, vars: Map[Expr, Rational]): Rational = tree match {
    case v @ Variable(id) =>  vars(v)
    case RealLiteral(v) => v
    case UMinusR(e) => - evalRational(e, vars)
    case PlusR(lhs, rhs) => evalRational(lhs, vars) + evalRational(rhs, vars)
    case MinusR(lhs, rhs) => evalRational(lhs, vars) - evalRational(rhs, vars)
    case TimesR(lhs, rhs) => evalRational(lhs, vars) * evalRational(rhs, vars)
    case DivisionR(lhs, rhs) => evalRational(lhs, vars) / evalRational(rhs, vars)
    //case SqrtR(e) => Rational(math.sqrt(evalRational(e, vars).toDouble)))
  }

  private def evalFixed(tree: Expr, vars: Map[Expr, Long]): Long = tree match {
    case v @ Variable(id) => vars(v)
    case LongLiteral(value) => value
    case UMinus(rhs) => - evalFixed(rhs, vars)
    case Plus(lhs, rhs) => evalFixed(lhs, vars) + evalFixed(rhs, vars)
    case Minus(lhs, rhs) => evalFixed(lhs, vars) - evalFixed(rhs, vars)
    case Times(lhs, rhs) => evalFixed(lhs, vars) * evalFixed(rhs, vars)
    case Division(lhs, rhs) => evalFixed(lhs, vars) / evalFixed(rhs, vars)
    case RightShift(e, bits) => evalFixed(e, vars) >> bits
    case LeftShift(e, bits) => evalFixed(e, vars) << bits
  }

  private def evalSingle(tree: Expr, vars: Map[Expr, (Float, Rational)]): (Float, Rational) = tree match {
    case v @ Variable(id) =>  vars(v)
    case RealLiteral(v) => (v.toFloat, v)
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
    case RealLiteral(v) => RationalInterval(v, v)
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
    case RealLiteral(v) => new XRationalForm(v)
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
        case r @ Record(id, lo, up, Some(absError), _, _) =>
          val interval = RationalInterval(lo, up)
          variableMap = variableMap + (Variable(id) -> (interval, absError))

        case Record(id, lo, up, None, _, None) =>
          val interval = RationalInterval(lo, up)
          variableMap = variableMap + (Variable(id) -> (interval, Rational.zero))
      }
    }
    variableMap
  }


}
