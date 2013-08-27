/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import Rational._
import purescala.Trees._

import real.Trees._

case class MismatchedException(msg: String) extends Exception(msg)

// the history may have to be sorted for comparisons
case class Index(val freshIndex: Int, val history: List[Int])

// Simplification of trees? There is some function in TreeOps already...
case class Magnitude(val value: Rational, val expr: Expr) {
  def unary_-(): Magnitude = Magnitude(-value, UMinus(expr))
  def *(factor: Rational): Magnitude = Magnitude(value * factor, Times(expr, RealLiteral(factor)))
  def +(y: Magnitude): Magnitude = Magnitude(this.value + y.value, Plus(expr, y.expr))
  def -(y: Magnitude): Magnitude = Magnitude(this.value - y.value, Minus(expr, y.expr))
  def *(y: Magnitude): Magnitude = Magnitude(this.value * y.value, Times(expr, y.expr))
}


object Deviation {
  var currIndex: Int = 0
  def newIndex: Int = {
    currIndex += 1
    assert(currIndex != Int.MaxValue, "Affine indices just ran out...")
    currIndex
  }

  def apply(i: Int, v: Rational): Deviation =
    Deviation(Index(i, List.empty), Magnitude(v, RealLiteral(v)))

  def apply(i: Int, hist: List[Int], v: Rational) : Deviation =
    Deviation(Index(i, hist), Magnitude(v, RealLiteral(v)))

  def apply(i: Int, hist: List[Int], v: Rational, variable: Variable) : Deviation =
    Deviation(Index(i, hist), Magnitude(v, variable))


  val dummyDev = Deviation(Index(Int.MaxValue, List.empty),
    Magnitude(Rational.zero, RealLiteral(Rational.zero)))

  var verbose = false
}

import Deviation._

case class Deviation(indx: Index, mgnt: Magnitude) {
  def unary_-(): Deviation = Deviation(indx, -mgnt)
  def *(factor: Rational): Deviation = Deviation(indx, mgnt * factor)
  def +(y: Deviation): Deviation = {
    assert(y.indx == this.indx) // will check both fresh and history
    Deviation(indx, this.mgnt + y.mgnt)
  }
  def -(y: Deviation): Deviation = {
    assert(y.indx == this.indx) // will check both fresh and history
    Deviation(indx, this.mgnt - y.mgnt)
  }
  def *(y: Deviation): Deviation = {
    Deviation(Index(newIndex, this.indx.history ++ y.indx.history),
              this.mgnt * y.mgnt)
  }

  override def toString: String = "%se%d".format(value.toString, index)
  
  def value: Rational = mgnt.value
  def index: Int = indx.freshIndex
  def isZero: Boolean = (mgnt.value == Rational.zero)
}
