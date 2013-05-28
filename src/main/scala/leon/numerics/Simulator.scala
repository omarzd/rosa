package leon
package numerics

import purescala.Trees._

import ceres.common._

class Simulator {

  val simSize = 10000000//0
  println("Simulation size: " + simSize + "\n")
  // Roundoff error is just the roundoff error, i.e. using the path of the float
  // @return (max range of floating-point output, max roundoff error of output)
  def simulate(name: String, tree: Expr, vars: Map[Variable, RationalInterval]): SimulationResult = {
    // TODO: for the actual run, seed shouldn't be fixed
    val r = new scala.util.Random(4753)

    var counter = 0
    var resInterval: Interval = EmptyInterval
    var maxRoundoff: Double = 0.0

    while(counter < simSize) {
      var randomInputs = new collection.immutable.HashMap[Variable, Rational]()

      for ((k, v) <- vars)
        randomInputs += ((k, v.xlo + Rational(r.nextDouble) * (v.xhi - v.xlo)))
      
      val (resDouble, resRat) = eval(tree, randomInputs)
      maxRoundoff = math.max(maxRoundoff, math.abs(resDouble - resRat.toDouble))
      resInterval = extendInterval(resInterval, resDouble)
      counter += 1
    }
    SimulationResult(name, resInterval, maxRoundoff)
  }

  private def extendInterval(i: Interval, d: Double): Interval = i match {
    case EmptyInterval => Interval(d)
    case NormalInterval(xlo, xhi) =>
      if (d >= xlo && d <= xhi) i
      else if (d <= xlo) NormalInterval(d, xhi)
      else if (d >= xhi) NormalInterval(xlo, d)
      else null
  }

  // We could probably use something fancy from TreeOps or evaluators
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

}
