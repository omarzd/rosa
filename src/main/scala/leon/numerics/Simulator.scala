package leon
package numerics

import purescala.Trees._
import purescala.Definitions._
import Utils.VariableCollector

import ceres.common._
import ceres.smartfloat._

import Precision._

class Simulator(reporter: Reporter) {

  val simSize = 100//0000//00
  reporter.info("Simulation size: " + simSize + "\n")

  def simulateThis(vc: VerificationCondition, precision: Precision) = {
    reporter.info("-----> Simulating function " + vc.funDef.id.name + "...")
    val funDef = vc.funDef

    val body = vc.body.get

    val inputs: Map[Variable, (RationalInterval, Rational)] = inputs2intervals(vc.inputs)

    val (maxRoundoff, resInterval) = precision match {
      case Float32 => runFloatSimulation(inputs, body)
      case Float64 => runDoubleSimulation(inputs, body)
    }

    val intInputs: Map[Expr, Interval] = inputs.map( x => (x._1 -> Interval(x._2._1.xlo.toDouble, x._2._1.xhi.toDouble) ))
    val smartInputs: Map[Expr, SmartFloat] = inputs.map ( x => (x._1 -> interval2smartfloat(x._2._1)) )

    vc.simulationRange = Some(resInterval)
    vc.rndoff = Some(maxRoundoff)
    vc.intervalRange = Some(evaluateInterval(body, intInputs))
    vc.smartfloatRange = Some(evaluateSmartFloat(body, smartInputs))
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
      val (resDouble, resRat) = evaluate(body, randomInputs)
      maxRoundoff = math.max(maxRoundoff, math.abs(resDouble - resRat.toDouble))
      resInterval = extendInterval(resInterval, resDouble)
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
      val (resDouble, resRat) = evaluateSingle(body, randomInputs)
      maxRoundoff = math.max(maxRoundoff, math.abs(resDouble - resRat.toDouble))
      resInterval = extendInterval(resInterval, resDouble)
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

  private def evaluateInterval(expr: Expr, vars: Map[Expr, Interval]): Interval = {
    val exprs: Seq[Expr] = expr match {
      case And(args) => args
      case _ => Seq(expr)
    }
    var currentVars: Map[Expr, Interval] = vars
    for (e <- exprs) e match {
      case Equals(variable, value) => currentVars = currentVars + (variable -> evalInterval(value, currentVars))
      case BooleanLiteral(true) => ;
      case _ => reporter.error("Simulation cannot handle: " + expr)
    }
    currentVars(ResultVariable())
  }

  private def evaluateSmartFloat(expr: Expr, vars: Map[Expr, SmartFloat]): SmartFloat = {
    val exprs: Seq[Expr] = expr match {
      case And(args) => args
      case _ => Seq(expr)
    }
    var currentVars: Map[Expr, SmartFloat] = vars
    for (e <- exprs) e match {
      case Equals(variable, value) => currentVars = currentVars + (variable -> evalSmartFloat(value, currentVars))
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

  private def evalInterval(tree: Expr, vars: Map[Expr, Interval]): Interval = tree match {
    case v @ Variable(id) => vars(v)
    case RationalLiteral(v) => Interval(v.toDouble)
    case IntLiteral(v) => Interval(v.toDouble)
    case UMinus(e) => - evalInterval(e, vars)
    case Plus(lhs, rhs) => evalInterval(lhs, vars) + evalInterval(rhs, vars)
    case Minus(lhs, rhs) => evalInterval(lhs, vars) - evalInterval(rhs, vars)
    case Times(lhs, rhs) => evalInterval(lhs, vars) * evalInterval(rhs, vars)
    case Division(lhs, rhs) => evalInterval(lhs, vars) / evalInterval(rhs, vars)
    case _ =>
      throw UnsupportedFragmentException("Can't handle: " + tree.getClass)
      EmptyInterval
  }

  private def evalSmartFloat(tree: Expr, vars: Map[Expr, SmartFloat]): SmartFloat = {

    val t = tree match {
    case v @ Variable(id) => vars(v)
    case RationalLiteral(v) => SmartFloat(v.toDouble)
    case IntLiteral(v) => SmartFloat(v.toDouble)
    case UMinus(e) => - evalSmartFloat(e, vars)
    case Plus(lhs, rhs) => evalSmartFloat(lhs, vars) + evalSmartFloat(rhs, vars)
    case Minus(lhs, rhs) => evalSmartFloat(lhs, vars) - evalSmartFloat(rhs, vars)
    case Times(lhs, rhs) => evalSmartFloat(lhs, vars) * evalSmartFloat(rhs, vars)
    case Division(lhs, rhs) => evalSmartFloat(lhs, vars) / evalSmartFloat(rhs, vars)
    case _ =>
      throw UnsupportedFragmentException("Can't handle: " + tree.getClass)
      null
    }
    println("evaluating: " + tree)
    println("result: " + t)
    t
  }

  private def interval2smartfloat(i: RationalInterval): SmartFloat = {
    val u = (i.xhi - i.xlo)/Rational(2.0)
    val d = i.xlo + u
    SmartFloat(d.toDouble, u.toDouble)
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
        rec.rndoff match {
          case Some(true) =>
            val interval = RationalInterval(rec.lo.get, rec.up.get)
            //val noise = affine.XFloat.roundoff(interval)
            variableMap = variableMap + (k -> (interval, Rational.zero))

          case None =>
            val interval = RationalInterval(rec.lo.get, rec.up.get)
            val noise = rec.noise.get
            variableMap = variableMap + (k -> (interval, noise))
        }
      }
    }
    variableMap
  }


}
