/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package real

import Rational._
import purescala.Trees._

import real.Trees._

//case class MismatchedException(msg: String) extends Exception(msg)


object Deviation {
  //private val bitLimit = 32

  var currIndex: Int = 0
  def newIndex: Int = {
    currIndex += 1
    assert(currIndex != Int.MaxValue, "Affine indices just ran out...")
    currIndex
  }

  /*def apply(i: Int, v: Rational): Deviation = {
    /*if (v.n.bitLength > bitLimit || v.d.bitLength > bitLimit) {
      //println("scaling")
      val scaled = if (v.n < 0) - scaleToLongUp(abs(v))
                   else scaleToLongUp(v)
      Deviation(Index(i, List.empty), Magnitude(scaled, RealLiteral(scaled)))

    } else {
    */
      //Deviation(Index(i, List.empty), Magnitude(v, RealLiteral(v)))
      Deviation(i, v) //Magnitude(v, RealLiteral(v)))
    //}
  }*/

  val dummyDev = Deviation(Int.MaxValue, Rational.zero)
    
  var verbose = false
}

import Deviation._

case class Deviation(index: Int, mgnt: Rational) {
  def unary_-(): Deviation = Deviation(index, -mgnt)
  def *(factor: Rational): Deviation = Deviation(index, mgnt * factor)
  def +(y: Deviation): Deviation = {
    assert(y.index == this.index)
    Deviation(index, this.mgnt + y.mgnt)
  }
  def -(y: Deviation): Deviation = {
    assert(y.index == this.index) 
    Deviation(index, this.mgnt - y.mgnt)
  }
  def *(y: Deviation): Deviation = {
    Deviation(newIndex, this.mgnt * y.mgnt)
  }

  override def toString: String = "%s(%d)".format(value.toString, index)

  def value: Rational = mgnt
  def isZero: Boolean = (mgnt == Rational.zero)
}
