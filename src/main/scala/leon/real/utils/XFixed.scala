/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees.{Expr, Variable}

import real.Trees._
import FixedPointFormat._
import XRationalForm._
import Rational._

object XFixed {

  def variables2xfixed(vars: VariablePool, config: XConfig, bits: Int, withRoundoff: Boolean = false): (Map[Expr, XFixed], Map[Int, Expr]) = {
    var variableMap: Map[Expr, XFixed] = Map.empty
    var indexMap: Map[Int, Expr] = Map.empty

    for(rec <- vars.getValidRecords) {
      rec match {
        case Record(v @ Variable(_), a @ Variable(_), Some(lo), Some(up), Some(unc)) =>
          val (xfixed, index) = xFixedWithUncertain(v, RationalInterval(lo, up), config, unc, withRoundoff, bits)
          variableMap = variableMap + (a -> xfixed)
          indexMap = indexMap + (index -> a)

        case Record(v @ Variable(_), a @ Variable(_), Some(lo), Some(up), None) =>
          val (xfixed, index) = xFixedWithRoundoff(v, RationalInterval(lo, up), config, bits)
          variableMap = variableMap + (a -> xfixed)
          indexMap = indexMap + (index -> a)

        case _ =>
          throw new Exception("bug!")
      }
    }
    (variableMap, indexMap)
  }

  // double constant (we include rdoff error)
  def apply(d: Double, config: XConfig, bits: Int): XFixed = {
    val r = rationalFromReal(d)
    val format = getFormat(r, bits)
    val rndoff = format.quantError
    val newError =
      if (!format.canRepresent(r))
        addNoise(new XRationalForm(Rational.zero), rndoff)
      else
        new XRationalForm(Rational.zero)
    new XFixed(format, RealLiteral(r), RationalInterval(r, r), newError, config)
  }

  // constant
  def apply(r: Rational, config: XConfig, bits: Int): XFixed = {
    val format = getFormat(r, bits)
    val rndoff = format.quantError
    val newError =
      if (!format.canRepresent(r))
        addNoise(new XRationalForm(Rational.zero), rndoff)
      else
        new XRationalForm(Rational.zero)
    new XFixed(format, RealLiteral(r), RationalInterval(r,r), newError, config)
  }

  def xFixedWithRoundoff(v: Variable, range: RationalInterval, config: XConfig, bits: Int): (XFixed, Int) = {
    val format = getFormat(range, bits)
    val rndoff = format.quantError
    val (newError, index) = addNoiseWithIndex(new XRationalForm(Rational.zero), rndoff)
    (new XFixed(format, v, range, newError, config), index)
  }

  def xFixedWithUncertain(v: Expr, range: RationalInterval, config: XConfig,
    uncertain: Rational, withRoundoff: Boolean, bits: Int): (XFixed, Int) = {
    assert(uncertain >= Rational.zero)

    var (newError, index) = addNoiseWithIndex(new XRationalForm(Rational.zero), uncertain)

    val format = getFormat(range + new RationalInterval(-uncertain, uncertain), bits)

    if (withRoundoff) {
      val rndoff = format.quantError
      (new XFixed(format, v, range, addNoise(newError, rndoff), config), index)
    } else {
      (new XFixed(format, v, range, newError, config), index)
    }
  }

}  

/*
  Assumes that all operands always have the same bitlength.
*/
// TODO: make this consistent with XFloat and put format at the end of the parameter list
class XFixed(val format: FixedPointFormat, val tr: Expr, val appInt: RationalInterval, val err: XRationalForm,
  val cnfg: XConfig) extends XReal(tr, appInt, err, cnfg) {

  //Assumes signed format.
  override def unary_-(): XReal = {
    if (!format.signed)
      throw IncompatibleFixedPointFormatsException("Unary minus not supported with unsigned format!")
    
    var (newTree, newRealRange, newError, newConfig) = super.negate
    new XFixed(format, newTree, newRealRange, newError, newConfig)
  }

  override def +(y: XReal): XReal = {
    assert(y.getClass == this.getClass)
    assert(this.format.bits == y.asInstanceOf[XFixed].format.bits)
    if (verbose) println("+fix " + this + " to " + y)
    var (newTree, newRealRange, newError, newConfig) = super.add(y)

    val newFormat = getFormat(newRealRange + newError.interval, format.bits)
    if (newFormat.f < math.max(this.format.f, y.asInstanceOf[XFixed].format.f)) { // we're loosing precision
      newError = addNoise(newError, newFormat.quantError)
    }

    new XFixed(format, newTree, newRealRange, newError, newConfig)
  }

  override def -(y: XReal): XReal = {
    assert(y.getClass == this.getClass)
    assert(this.format.bits == y.asInstanceOf[XFixed].format.bits)
    if (verbose) println("-fl " + this + " from " + y)
    var (newTree, newRealRange, newError, newConfig) = super.subtract(y)

    val newFormat = getFormat(newRealRange + newError.interval, format.bits)
    if (newFormat.f < math.max(this.format.f, y.asInstanceOf[XFixed].format.f)) { // we're loosing precision
      newError = addNoise(newError, newFormat.quantError)
    }

    new XFixed(format, newTree, newRealRange, newError, newConfig)
  }


  override def *(y: XReal): XReal = {
    assert(y.getClass == this.getClass)
    assert(this.format.bits == y.asInstanceOf[XFixed].format.bits, "bits do not match: " + this.format.bits + "  " + y.asInstanceOf[XFixed].format.bits)
    if (verbose) println("*fl " + this.tree + " with " + y.tree)
    if (verbose) println("x.error: " + this.error.longString)
    if (verbose) println("y.error: " + y.error.longString)
    var (newTree, newRealRange, newError, newConfig) = super.multiply(y)

    val newFormat = getFormat(newRealRange + newError.interval, format.bits)
    if (newFormat.f < this.format.f + y.asInstanceOf[XFixed].format.f) { //loosing precision
      // TODO: if (!exactConstantMultiplication || (this.qRadius != 0.0 && y.qRadius != 0.0))
      newError = addNoise(newError, newFormat.quantError)
    }
    new XFixed(format, newTree, newRealRange, newError, newConfig)
  }


  override def /(y: XReal): XReal = {
    assert(y.getClass == this.getClass)
    if (verbose) println("/fl " + this.tree + " with " + y.tree)
    var (newTree, newRealRange, newError, newConfig) = super.divide(y)

    val newFormat = getFormat(newRealRange + newError.interval, format.bits)
    assert(newFormat.bits == this.format.bits,
      "New format has wrong number of bits %d (vs %d)".format(newFormat.bits, this.format.bits))
    
    newError = addNoise(newError, newFormat.quantError)
    new XFixed(format, newTree, newRealRange, newError, newConfig)
  }

  override def squareRoot: XReal = {
    throw new Exception("Square root not implemented for fixed-points")
    null
    /*var (newTree, newRealRange, newError, newConfig) = super.takeSqrtRoot
    val rndoff = roundoff(newRealRange + newError.interval)
    newError = addNoise(newError, rndoff)
    return new XFloat(newTree, newRealRange, newError, newConfig)
    */
  }


  override def toString: String = "%s -x (%.16g,%s)".format(this.interval.toString, this.maxError.toDouble, this.format)

}