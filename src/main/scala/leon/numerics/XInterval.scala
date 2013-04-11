package leon
package numerics

import ceres.common.{Rational, Interval, RationalInterval}
import ceres.affine.{RationalForm}

import purescala.Trees._

object XInterval {
  //def apply(d: Double) = new XInterval(Map.empty,
  //  RationalLiteral(Rational.rationalFromReal(d)),
  //  new RationalForm(Rational.rationalFromReal(d)))
  def apply(r: Rational, solver: NumericSolver) = new XInterval(Map.empty, RationalLiteral(r),
    new RationalForm(r), solver)

  //def apply(v: Variable, a: Double, b: Double) = {
  //  val int = RationalInterval(Rational.rationalFromReal(a),
  //                              Rational.rationalFromReal(b))
  //  new XInterval(Map(v -> int), v, RationalForm(int))
  //}

  def apply(v: Variable, a: Rational, b: Rational, solver: NumericSolver) = {
    val int = RationalInterval(a, b)
    new XInterval(Map(v -> int), v, RationalForm(int), solver)
  }
  // there is duplication here
  // This method allows us to define the affine forms such that several
  // uses of the same variable will have the same affine form (same indices)
  //def apply(v: Variable, a: Double, b: Double, aform: RationalForm) = {
  //  val int = RationalInterval(Rational.rationalFromReal(a),
  //                              Rational.rationalFromReal(b))
  //  new XInterval(Map(v -> int), v, aform)
  //}
}


/**
  A datatype that performs range arithmetic with the help of a constraint solver.
  Returns intervals sound wrt. to reals, not floats.
 */
class XInterval(val variables: Map[Variable, RationalInterval],
  val tree: Expr, val approx: RationalForm, solver: NumericSolver) {

  // TODO: we could (sanity) check that approx is indeed AA(tree)

  def unary_-(): XInterval = new XInterval(variables, FUMinus(tree), -approx, solver)

  def +(y: XInterval): XInterval =
    new XInterval(this.variables ++ y.variables, FPlus(this.tree, y.tree),
      this.approx + y.approx, solver)

  def -(y: XInterval): XInterval =
    new XInterval(this.variables ++ y.variables, FMinus(this.tree, y.tree),
      this.approx - y.approx, solver)

  def *(y: XInterval): XInterval = {
    /*println("multiplying " + this.tree + "  *  " + y.tree)
    println("approx. x :" + approx.x0 + "  -  " + approx.noise)
    println("approx. y :" + y.approx.x0 + "  -  " + y.approx.noise)
    */
    new XInterval(this.variables ++ y.variables, FTimes(this.tree, y.tree),
      this.approx * y.approx, solver)
  }

  def /(y: XInterval): XInterval =
    new XInterval(this.variables ++ y.variables, FDivision(this.tree, y.tree),
      this.approx / y.approx, solver)

  override def toString: String = //"%s -> %s".format(interval.toString, tree.toString)
    interval.toString

  def interval: RationalInterval = {
    BoundsIterator.tightenRange(solver, variables, tree, new RationalInterval(approx.intervalDouble))
  }

  // TODO: cache results
  def intervalDouble: Interval = {
    //val newIntLinear = IntervalBounds.determineRangeLinear(tree, new RationalInterval(approx.interval))
    val newIntBinary = BoundsIterator.tightenRange(solver, variables, tree, new RationalInterval(approx.intervalDouble))
    //newIntBinary.toInterval
    approx.intervalDouble
  }
  /*def /(y: XInterval): XInterval

  def squareRoot: XInterval
  def ln: XInterval
  def exponential: XInterval

  def cosine: XInterval
  def sine: XInterval
  def tangent: XInterval

  def arccosine: XInterval
  def arcsine: XInterval
  def arctangent: XInterval
  */
}
