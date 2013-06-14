package leon
package numerics

import purescala.Trees._
import purescala.Definitions._
import Utils.VariableCollector

import ceres.common._

class Simulator(reporter: Reporter) {

  val simSize = 1000000//00
  reporter.info("Simulation size: " + simSize + "\n")

  // Roundoff error is just the roundoff error, i.e. using the path of the float
  def simulateThis(vc: VerificationCondition) = {
    reporter.info("-----> Simulating function " + vc.funDef.id.name + "...")
    val funDef = vc.funDef

    // TODO: for the actual run, seed shouldn't be fixed
    val r = new scala.util.Random(4753)

    val body = funDef.body.get
    // We don't use the noise for now, but maybe later
    val inputs: Map[Variable, (RationalInterval, Rational)] = funDef.precondition match {
      case Some(p) =>
        val collector = new VariableCollector
        collector.transform(p)
        inputs2intervals(collector.recordMap)
      case None =>
        Map.empty
    }

    var counter = 0
    var resInterval: Interval = EmptyInterval
    var maxRoundoff: Double = 0.0

    while(counter < simSize) {
      var randomInputs = new collection.immutable.HashMap[Variable, Rational]()

      for ((k, ((i, n))) <- inputs)
        randomInputs += ((k, i.xlo + Rational(r.nextDouble) * (i.xhi - i.xlo)))

      val (resDouble, resRat) = eval(body, randomInputs)
      maxRoundoff = math.max(maxRoundoff, math.abs(resDouble - resRat.toDouble))
      resInterval = extendInterval(resInterval, resDouble)
      counter += 1
    }

    val intInputs = inputs.map( x => (x._1 -> Interval(x._2._1.xlo.toDouble, x._2._1.xhi.toDouble) ))

    vc.simulationRange = Some(resInterval)
    vc.rndoff = Some(maxRoundoff)
    vc.intervalRange = Some(evalInterval(body, intInputs))
    //SimulationResult(funDef.id.name, resInterval, maxRoundoff, evalInterval(body, intInputs))
  }

  private def extendInterval(i: Interval, d: Double): Interval = i match {
    case EmptyInterval => Interval(d)
    case NormalInterval(xlo, xhi) =>
      if (d >= xlo && d <= xhi) i
      else if (d <= xlo) NormalInterval(d, xhi)
      else if (d >= xhi) NormalInterval(xlo, d)
      else null
  }

  // This thing with Rationals does not work with sqrt...
  private def eval(tree: Expr, vars: Map[Variable, Rational]): (Double, Rational) = tree match {
    case v @ Variable(id) =>
      val ratValue = vars(v)
      val dblValue = ratValue.toDouble // uses BigDecimal, so this should be accurate
      (dblValue, ratValue)
    case RationalLiteral(v) =>
      (v.toDouble, v)
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

  private def evalInterval(tree: Expr, vars: Map[Variable, Interval]): Interval = tree match {
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


  private def inputs2intervals(vars: Map[Variable, Record]): Map[Variable, (RationalInterval, Rational)] = {
    var variableMap: Map[Variable, (RationalInterval, Rational)] = Map.empty

    for((k, rec) <- vars) {
      if (rec.isComplete) {
        rec.rndoff match {
          case Some(true) =>
            val interval = RationalInterval(rec.lo.get, rec.up.get)
            val noise = affine.XFloat.roundoff(interval)
            variableMap = variableMap + (k -> (interval, noise))

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
