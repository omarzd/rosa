package leon
package numerics

import ceres.common.{Rational, RationalInterval}
import ceres.affine.{RationalForm}
import Rational._
import RationalForm._

import purescala.Trees._

// This can go once we fix the contruction below
import java.math.{BigInteger, BigDecimal}

/**
  TODO:
  - make this cache the interval values so we don't run Z3 unnecessarily

 */

object XFloat {

  // double constant (we include rdoff error)
  def apply(d: Double): XFloat = {
    val rd = Rational(d)
    val newRange = XInterval(rd)
    val rndoff = roundoff(rd)
    val newError = addNoise(rndoff, new RationalForm(Rational(0l, 1l)))
    return new XFloat(newRange, newError)
  }

  // constant
  def apply(r: Rational): XFloat = {
    val newRange = XInterval(r)
    val newError = new RationalForm(Rational(0l, 1l))
    return new XFloat(newRange, newError)
  }

  // variable
  def apply(v: Variable, a: Rational, b: Rational): XFloat = {
    val newRange = XInterval(v, a, b)
    val rndoff = roundoff(RationalInterval(a, b)) // another version of that fnc?
    val newError = addNoise(rndoff, new RationalForm(Rational(0l, 1l)))
    return new XFloat(newRange, newError)
  }

  // Unit roundoff
  val u = Rational(new BigInt(new BigInteger("1")),
    new BigInt(new BigInteger("2")).pow(53))

  // Always return a positive number
  def roundoff(range: RationalInterval): Rational = {
    val maxAbs = max(abs(range.xlo), abs(range.xhi))
    return u * maxAbs 
  }

  def roundoff(r: Rational): Rational = {
    return u * abs(r)
  }

  val verbose = false
}


class XFloat(val realRange: XInterval, val error: RationalForm) {
  import XFloat._

  // This assertion is incorrect, because we use an optimization for
  // computing multiplications for RationalForm
  //assert(error.x0 == Rational(0.0), "midpoint of errors is: " + error.x0)

  def interval: RationalInterval = {
    realRange.interval + error.interval
  }

  def maxRoundoff: Rational = {
    val i = error.interval
    return max(abs(i.xlo), abs(i.xhi))
  }

  def unary_-(): XFloat = new XFloat(-realRange, -error)

  //i.e. compute new real range, propagate errors, add new roundoff
  // To be 100% correct, there is also a contribution from the old errors,
  // (this.error + y.error) * \delta^2
  def +(y: XFloat): XFloat = {
    val newRange = this.realRange + y.realRange
    val rndoff = roundoff(newRange.interval)
    val newError = addNoise(rndoff, this.error + y.error)
    if(verbose) println("\naddition, newRange: " + newRange)
    if(verbose) println("            roundoff: " + rndoff)
    return new XFloat(newRange, newError)
  }

  def -(y: XFloat): XFloat = {
    val newRange = this.realRange - y.realRange
    val rndoff = roundoff(newRange.interval)
    val newError = addNoise(rndoff, this.error - y.error)
    if(verbose) println("\nsubtraction, newRange: " + newRange)
    if(verbose) println("               roundoff: " + rndoff)
    return new XFloat(newRange, newError)
  }

  def *(y: XFloat): XFloat = {
    val newRange = this.realRange * y.realRange
    val rndoff = roundoff(newRange.interval)
    
    val xAA = RationalForm(this.realRange.interval)
    val yAA = RationalForm(y.realRange.interval)
    val yErr = y.error
    val xErr = this.error
    val newError = addNoise(rndoff, xAA*yErr + yAA*xErr + xErr*yErr)
    if(verbose) println("\nmultiplication, newRange: " + newRange)
    if(verbose) println("                  roundoff: " + rndoff)
    return new XFloat(newRange, newError)
  }

  // TODO: check the constant thing is fine
  def /(y: XFloat): XFloat = {
    // TODO: catch division by zero

    //if (y.isExact) {
      

    // Compute approximation
    val kAA = RationalForm((XInterval(1.0) / y.realRange).interval)
    val xAA = RationalForm(this.realRange.interval)
    val xErr = this.error

    val yInt = y.interval
    val a = min(abs(yInt.xlo), abs(yInt.xhi))
    // make this negOne constant or sth like that
    val errorMultiplier = Rational(-1l, 1l) / (a*a)
    val gErr = y.error * new RationalForm(errorMultiplier)
    
    val newRange = this.realRange / y.realRange
    val rndoff = roundoff(newRange.interval)
    val newError = addNoise(rndoff, xAA*gErr + kAA*xErr + xErr*gErr)
    if(verbose) println("\ndivision, newRange: " + newRange)
    if(verbose) println("            roundoff: " + rndoff)
    return new XFloat(newRange, newError)
  }

  override def toString: String = this.interval.toString + " - (" +
    this.maxRoundoff + ")(abs)" 

}