package leon
package numerics

import purescala.Trees._
import purescala.Definitions._
import Utils.VariableCollector

import ceres.common.{Interval, EmptyInterval, NormalInterval}
import affine._

import Precision._

class Simulator(reporter: Reporter) {

  val simSize = 1000000//00
  reporter.info("Simulation size: " + simSize + "\n")

  def simulateThis(vc: VerificationCondition, precision: Precision) = {
    reporter.info("-----> Simulating function " + vc.funDef.id.name + "...")
    val funDef = vc.funDef

    val body = vc.body

    val inputs: Map[Variable, (RationalInterval, Rational)] = inputs2intervals(vc.inputs)

    val (maxRoundoff, resInterval) = precision match {
      case Float32 => runFloatSimulation(inputs, body)
      case Float64 => runDoubleSimulation(inputs, body)
    }
    //val (maxRoundoff, resInterval) = (0.0, Interval(0.0) )

    val intInputs: Map[Expr, RationalInterval] = inputs.map( x => (x._1 -> RationalInterval(x._2._1.xlo, x._2._1.xhi) ))
    val xratInputs: Map[Expr, XRationalForm] = inputs.map ( x => (x._1 -> XRationalForm(x._2._1) ) )

    vc.simulationRange = Some(resInterval)
    vc.rndoff = Some(maxRoundoff)
    //vc.intervalRange = Some(evaluateInterval(body, intInputs))
    //vc.affineRange = Some(evaluateXRationalForm(body, xratInputs).interval)
    //reporter.info("Interval range: " + vc.intervalRange.get)
    //reporter.info("Affine range:   " + vc.affineRange.get)
    reporter.info("Simulated interval: " + vc.simulationRange)
    reporter.info("Max error: " + vc.rndoff.get)
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
        case _ => ;
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
        case _ => ;
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
    case IntLiteral(v) => (v.toDouble, Rational(v))
    case UMinus(e) =>
      val (eDbl, eRat) = eval(e, vars)
      (-eDbl, -eRat)
    case Plus(lhs, rhs) =>
      val (lhsDbl, lhsRat) = eval(lhs, vars)
      val (rhsDbl, rhsRat) = eval(rhs, vars)
      (lhsDbl + rhsDbl, lhsRat + rhsRat)
    case Minus(lhs, rhs) =>
      val (lhsDbl, lhsRat) = eval(lhs, vars)
      val (rhsDbl, rhsRat) = eval(rhs, vars)
      (lhsDbl - rhsDbl, lhsRat - rhsRat)
    case Times(lhs, rhs) =>
      val (lhsDbl, lhsRat) = eval(lhs, vars)
      val (rhsDbl, rhsRat) = eval(rhs, vars)
      (lhsDbl * rhsDbl, lhsRat * rhsRat)
    case Division(lhs, rhs) =>
      val (lhsDbl, lhsRat) = eval(lhs, vars)
      val (rhsDbl, rhsRat) = eval(rhs, vars)
      (lhsDbl / rhsDbl, lhsRat / rhsRat)

    case _ =>
      throw UnsupportedFragmentException("Can't handle: " + tree.getClass)
      (Double.NaN, Rational(0))
  }

  private def evalSingle(tree: Expr, vars: Map[Expr, (Float, Rational)]): (Float, Rational) = tree match {
    case v @ Variable(id) =>  vars(v)
    case RationalLiteral(v) => (v.toFloat, v)
    case IntLiteral(v) => (v.toFloat, Rational(v))
    case UMinus(e) =>
      val (eDbl, eRat) = evalSingle(e, vars)
      (-eDbl, -eRat)
    case Plus(lhs, rhs) =>
      val (lhsDbl, lhsRat) = evalSingle(lhs, vars)
      val (rhsDbl, rhsRat) = evalSingle(rhs, vars)
      (lhsDbl + rhsDbl, lhsRat + rhsRat)
    case Minus(lhs, rhs) =>
      val (lhsDbl, lhsRat) = evalSingle(lhs, vars)
      val (rhsDbl, rhsRat) = evalSingle(rhs, vars)
      (lhsDbl - rhsDbl, lhsRat - rhsRat)
    case Times(lhs, rhs) =>
      val (lhsDbl, lhsRat) = evalSingle(lhs, vars)
      val (rhsDbl, rhsRat) = evalSingle(rhs, vars)
      (lhsDbl * rhsDbl, lhsRat * rhsRat)
    case Division(lhs, rhs) =>
      val (lhsDbl, lhsRat) = evalSingle(lhs, vars)
      val (rhsDbl, rhsRat) = evalSingle(rhs, vars)
      (lhsDbl / rhsDbl, lhsRat / rhsRat)

    case _ =>
      throw UnsupportedFragmentException("Can't handle: " + tree.getClass)
      (Float.NaN, Rational(0))
  }

  private def evalInterval(tree: Expr, vars: Map[Expr, RationalInterval]): RationalInterval = tree match {
    case v @ Variable(id) => vars(v)
    case RationalLiteral(v) => RationalInterval(v, v)
    case IntLiteral(v) => RationalInterval(Rational(v), Rational(v))
    case UMinus(e) => - evalInterval(e, vars)
    case Plus(lhs, rhs) => evalInterval(lhs, vars) + evalInterval(rhs, vars)
    case Minus(lhs, rhs) => evalInterval(lhs, vars) - evalInterval(rhs, vars)
    case Times(lhs, rhs) => evalInterval(lhs, vars) * evalInterval(rhs, vars)
    case Division(lhs, rhs) => evalInterval(lhs, vars) / evalInterval(rhs, vars)
    case _ =>
      throw UnsupportedFragmentException("Can't handle: " + tree.getClass)
      null
  }

  private def evalXRationalForm(tree: Expr, vars: Map[Expr, XRationalForm]): XRationalForm = {
    val t = tree match {
    case v @ Variable(id) => vars(v)
    case RationalLiteral(v) => new XRationalForm(v)
    case IntLiteral(v) => new XRationalForm(Rational(v))
    case UMinus(e) => - evalXRationalForm(e, vars)
    case Plus(lhs, rhs) => evalXRationalForm(lhs, vars) + evalXRationalForm(rhs, vars)
    case Minus(lhs, rhs) => evalXRationalForm(lhs, vars) - evalXRationalForm(rhs, vars)
    case Times(lhs, rhs) => evalXRationalForm(lhs, vars) * evalXRationalForm(rhs, vars)
    case Division(lhs, rhs) => evalXRationalForm(lhs, vars) / evalXRationalForm(rhs, vars)
    case _ =>
      throw UnsupportedFragmentException("Can't handle: " + tree.getClass)
      null
    }
    //println("\nevaluating: " + tree)
    //println("result: " + t)
    //println("x0: " + t.x0)
    //println("noise: " + t.noise)
    t
  }

  private def extendInterval(i: Interval, d: Double): Interval = i match {
    case EmptyInterval => Interval(d)
    case NormalInterval(xlo, xhi) =>
      if (d >= xlo && d <= xhi) i
      else if (d <= xlo) NormalInterval(d, xhi)
      else if (d >= xhi) NormalInterval(xlo, d)
      else null
  }

  private def inputs2intervals(vars: Map[Variable, Record]): Map[Variable, (RationalInterval, Rational)] = {
    var variableMap: Map[Variable, (RationalInterval, Rational)] = Map.empty

    for((k, rec) <- vars) {
      if (rec.isComplete) {
        rec.absNoise match {
          case Some(n) =>
            val interval = RationalInterval(rec.lo.get, rec.up.get)
            variableMap = variableMap + (k -> (interval, n))

          case None =>
            val interval = RationalInterval(rec.lo.get, rec.up.get)
            //val noise = affine.XFloat.roundoff(interval)
            variableMap = variableMap + (k -> (interval, Rational.zero))
        }
      }
    }
    variableMap
  }


}
