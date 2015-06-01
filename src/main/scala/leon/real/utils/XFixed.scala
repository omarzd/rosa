/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package real

import purescala.Trees.{Expr, Variable}

import real.Trees._
import FixedPointFormat._
import RationalForm._
import Rational._

object XFixed {

  def variables2xfixed(vars: Iterable[Record], config: XConfig, bits: Int, withRoundoff: Boolean = false): Map[Expr, XFixed] = {
    var variableMap: Map[Expr, XFixed] = Map.empty
    
    for(rec <- vars) {
      rec match {
        case r @ Record(id, lo, up, Some(absError), aId, _) =>
          val xfixed = xFixedWithUncertain(Variable(id), RationalInterval(lo, up), config, absError,
            withRoundoff, bits)
          variableMap = variableMap + (Variable(aId) -> xfixed)
          
        case Record(id, lo, up, None, aId, None) if (rec.isInteger) =>
          val xfixed = xFixedExact(Variable(id), RationalInterval(lo, up), config, bits)      
          variableMap = variableMap + (Variable(aId) -> xfixed)

        case Record(id, lo, up, None, aId, None) =>
          val xfixed = xFixedWithRoundoff(Variable(id), RationalInterval(lo, up), config, bits)
          variableMap = variableMap + (Variable(aId) -> xfixed)
    
        case _ =>
          throw new Exception("bug!")
      }
    }
    variableMap
  }

   def variables2xfixedExact(vars: Iterable[Record], config: XConfig, bits: Int): Map[Expr, XFixed] = {
    var variableMap: Map[Expr, XFixed] = Map.empty
    
    for(rec <- vars) {
      rec match {

        case Record(id, lo, up, _, aId, _) =>
          val xfixed = xFixedExact(Variable(id), RationalInterval(lo, up), config, bits)
          variableMap = variableMap + (Variable(aId) -> xfixed)

        case _ =>
          throw new Exception("bug!")
      }
    }
    variableMap
  }

  def variables2xfixedActualExact(vars: Iterable[Record], config: XConfig, bits: Int): Map[Expr, XFixed] = {
    var variableMap: Map[Expr, XFixed] = Map.empty
    
    for(rec <- vars) {
      rec match {
        case Record(id, lo, up, _, aId, _) if rec.isInteger =>
          val xfloat = xFixedExact(Variable(id), RationalInterval(lo, up), config, bits)
          variableMap = variableMap + (Variable(aId) -> xfloat)


        case Record(id, lo, up, _, aId, _) =>
          val xfloat = xFixedExact(Variable(id), RationalInterval(rec.loAct.get, rec.upAct.get), config, bits)
          variableMap = variableMap + (Variable(aId) -> xfloat)

        case _ =>
          throw new Exception("bug!")
      }
    }
    variableMap
  }

  // double constant (we include rdoff error)
  def apply(d: Double, config: XConfig, bits: Int): XFixed = {
    val r = rationalFromReal(d)
    val format = getFormat(r, bits)
    val rndoff = format.quantError
    val newError =
      if (!format.canRepresent(r))
        new RationalForm(Rational.zero) :+ rndoff
      else
        new RationalForm(Rational.zero)
    new XFixed(format, RealLiteral(r), RationalInterval(r, r), newError, config)
  }

  // constant
  def apply(r: Rational, config: XConfig, bits: Int): XFixed = {
    val format = getFormat(r, bits)
    val rndoff = format.quantError
    val newError =
      if (!format.canRepresent(r))
        new RationalForm(Rational.zero) :+ rndoff
      else
        new RationalForm(Rational.zero)
    new XFixed(format, RealLiteral(r), RationalInterval(r,r), newError, config)
  }

  def xFixedWithRoundoff(v: Variable, range: RationalInterval, config: XConfig, bits: Int): XFixed = {
    val format = getFormat(range, bits)
    val rndoff = format.quantError
    val newError = new RationalForm(Rational.zero) :+ rndoff
    new XFixed(format, v, range, newError, config)
  }

  def xFixedExact(v: Variable, range: RationalInterval, config: XConfig, bits: Int): XFixed = {
    val format = getFormat(range, bits)
    new XFixed(format, v, range, new RationalForm(Rational.zero), config)
  }

  def xFixedWithUncertain(v: Expr, range: RationalInterval, config: XConfig,
    uncertain: Rational, withRoundoff: Boolean, bits: Int): XFixed = {
    assert(uncertain >= Rational.zero)

    var newError = new RationalForm(Rational.zero) :+ uncertain

    val format = getFormat(range + new RationalInterval(-uncertain, uncertain), bits)

    if (withRoundoff) {
      val rndoff = format.quantError
      new XFixed(format, v, range, newError :+ rndoff, config)
    } else {
      new XFixed(format, v, range, newError, config)
    }
  }

}

/*
  Assumes that all operands always have the same bitlength.
*/
// TODO: make consistent with XFloat and put format at the end of the parameter list
class XFixed(val format: FixedPointFormat, val tr: Expr, val appInt: RationalInterval, val err: RationalForm,
  val cnfg: XConfig, val Z3tmOut: Int = 0) extends XReal(tr, appInt, err, cnfg, Z3tmOut) {

  override def cleanConfig: XReal = {
    new XFixed(format, tree, approxInterval, error, getCleanConfig)
  }

  //Assumes signed format.
  override def unary_-(): XReal = {
    if (!format.signed)
      throw IncompatibleFixedPointFormatsException("Unary minus not supported with unsigned format!")

    var (newTree, newRealRange, newError, newConfig, tmOut) = super.negate
    new XFixed(format, newTree, newRealRange, newError, newConfig, tmOut)
  }

  override def +(y: XReal): XReal = {
    assert(y.getClass == this.getClass)
    assert(this.format.bits == y.asInstanceOf[XFixed].format.bits)
    if (verbose) println("+fix " + this.tree + " to " + y.tree)
    var (newTree, newRealRange, newError, newConfig, tmOut) = super.add(y)

    val newFormat = getFormat(newRealRange + newError.interval, format.bits)
    if (newFormat.f < math.max(this.format.f, y.asInstanceOf[XFixed].format.f)) { // we're loosing precision
      newError = newError :+ newFormat.quantError
    }

    new XFixed(newFormat, newTree, newRealRange, newError, newConfig, tmOut)
  }

  override def -(y: XReal): XReal = {
    assert(y.getClass == this.getClass)
    assert(this.format.bits == y.asInstanceOf[XFixed].format.bits)
    if (verbose) println("-fl " + this + " from " + y)
    var (newTree, newRealRange, newError, newConfig, tmOut) = super.subtract(y)

    val newFormat = getFormat(newRealRange + newError.interval, format.bits)
    if (newFormat.f < math.max(this.format.f, y.asInstanceOf[XFixed].format.f)) { // we're loosing precision
      newError = newError :+ newFormat.quantError
    }

    new XFixed(newFormat, newTree, newRealRange, newError, newConfig, tmOut)
  }


  override def *(y: XReal): XReal = {
    assert(y.getClass == this.getClass, y.getClass + " vs " + this.getClass)
    assert(this.format.bits == y.asInstanceOf[XFixed].format.bits, "bits do not match: " + this.format.bits + "  " + y.asInstanceOf[XFixed].format.bits)
    if (verbose) println("*fl " + this.tree + " with " + y.tree)
    if (verbose) println("x.error: " + this.error.longString)
    if (verbose) println("y.error: " + y.error.longString)
    var (newTree, newRealRange, newError, newConfig, tmOut) = super.multiply(y)

    val newFormat = getFormat(newRealRange + newError.interval, format.bits)
    if (newFormat.f < this.format.f + y.asInstanceOf[XFixed].format.f) { //loosing precision
      // TODO: if (!exactConstantMultiplication || (this.qRadius != 0.0 && y.qRadius != 0.0))
      newError = newError :+ newFormat.quantError
    }    
    new XFixed(newFormat, newTree, newRealRange, newError, newConfig, tmOut)
  }


  override def /(y: XReal): XReal = {
    assert(y.getClass == this.getClass)
    if (verbose) println("/fl " + this.tree + " with " + y.tree)
    var (newTree, newRealRange, newError, newConfig, tmOut) = super.divide(y)

    val newFormat = getFormat(newRealRange + newError.interval, format.bits)
    assert(newFormat.bits == this.format.bits,
      "New format has wrong number of bits %d (vs %d)".format(newFormat.bits, this.format.bits))

    newError = newError :+ newFormat.quantError
    new XFixed(newFormat, newTree, newRealRange, newError, newConfig, tmOut)
  }

  override def squareRoot: XReal = {
    throw new SqrtNotImplementedException("Square root not implemented for fixed-points")
    null
    /*var (newTree, newRealRange, newError, newConfig) = super.takeSqrtRoot
    val rndoff = roundoff(newRealRange + newError.interval)
    newError = addNoise(newError, rndoff)
    new XFloat(newTree, newRealRange, newError, newConfig)
    */
  }


  override def toString: String = "%s -x (%.16g,%s)".format(this.interval.toString, this.maxError.toDouble, this.format)

}
