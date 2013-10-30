/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees.{Expr, Variable, And, Equals, LessEquals}
import real.Trees._

import real.Trees.RealLiteral
import Rational._
import XRationalForm._
import RationalAffineUtils._
import VariableShop._

import collection.mutable.Queue
import java.math.{BigInteger, BigDecimal}

object XFloat {

  /**
    Converts variable-record pairs into XFloats.
    Discards all variables for which neither rndoff nor noise has been specified.
    Index is the index of the main uncertainty, not the roundoff.
    @param vars what we want to convert
    @param config solver, precondition, which precision to choose
    @param withRoundoff whether the initial XFloat should also get an roundoff error, additionally to the noise
   */
  def variables2xfloats(vars: VariablePool, config: XConfig, machineEps: Rational, withRoundoff: Boolean = false): (Map[Expr, XFloat], Map[Int, Expr]) = {
    var variableMap: Map[Expr, XFloat] = Map.empty
    var indexMap: Map[Int, Expr] = Map.empty

    for(rec <- vars.getValidRecords) {
      rec match {
        case Record(v @ Variable(_), a @ Variable(_), Some(lo), Some(up), Some(unc)) =>
          val (xfloat, index) = XFloat.xFloatWithUncertain(v, RationalInterval(lo, up), config, unc, withRoundoff, machineEps)
          variableMap = variableMap + (a -> xfloat)
          indexMap = indexMap + (index -> a)

        case Record(v @ Variable(_), a @ Variable(_), Some(lo), Some(up), None) =>
          val (xfloat, index) = XFloat.xFloatWithRoundoff(v, RationalInterval(lo, up), config, machineEps)
          variableMap = variableMap + (a -> xfloat)
          indexMap = indexMap + (index -> a)

        case _ =>
          throw new Exception("bug!")
      }

        /*(rec.absNoise, rec.relNoise) match { // was already checked that only one is possible
          case (Some(n), None) =>
            // index is the index of the main uncertainty, not the roundoff
            val (xfloat, index) = XFloat.xFloatWithUncertain(k,
                    RationalInterval(rec.lo.get, rec.up.get),
                    config, n, withRoundoff)
            variableMap = variableMap + (k -> xfloat)
            indexMap = indexMap + (index -> k)

          case (None, Some(factor)) =>
            val maxError = factor * max(abs(rec.lo.get), abs(rec.up.get))
            // index is the index of the main uncertainty, not the roundoff
            val (xfloat, index) = XFloat.xFloatWithUncertain(k,
                    RationalInterval(rec.lo.get, rec.up.get),
                    config, maxError, withRoundoff)
            variableMap = variableMap + (k -> xfloat)
            indexMap = indexMap + (index -> k)

          case (None, None) => // default roundoff
            val (xfloat, index) = XFloat.xFloatWithRoundoff(k,
                    RationalInterval(rec.lo.get, rec.up.get), config)
            variableMap = variableMap + (k -> xfloat)
            indexMap = indexMap + (index -> k)
        }*/
    }
    (variableMap, indexMap)
  }


  // double constant (we include rdoff error)
  def apply(d: Double, config: XConfig, machineEps: Rational): XFloat = {
    val r = rationalFromReal(d)
    val rndoff = roundoff(r, machineEps)
    val newError = addNoise(new XRationalForm(Rational.zero), rndoff)
    new XFloat(RealLiteral(r), RationalInterval(r, r), newError, config, machineEps)
  }

  // constant
  def apply(r: Rational, config: XConfig, machineEps: Rational): XFloat = {
    val newError = new XRationalForm(Rational.zero)
    new XFloat(RealLiteral(r), RationalInterval(r,r), newError, config, machineEps)
  }

  /**
    Creates an XFloat and adds the max roundoff error over the range automatically.
    @param v variable associated with this XFloat
    @param range real-valued range of this XFloat
    @param config solver, precondition, which precision to choose
  **/
  def xFloatWithRoundoff(v: Variable, range: RationalInterval, config: XConfig, machineEps: Rational): (XFloat, Int) = {
    val rndoff = roundoff(range, machineEps)
    val (newError, index) = addNoiseWithIndex(new XRationalForm(Rational.zero), rndoff)
    return (new XFloat(v, range, newError, config, machineEps), index)
  }

  /**
    Creates an XFloat with a given uncertainty.
    @param v variable associated with this XFloat
    @param range real-valued range of this XFloat
    @param solver solver, precondition, which precision to choose
    @param uncertain max uncertainty
    @param withRoundoff if true an additional roundoff error will be added automatically, additionally to noise
  **/
  def xFloatWithUncertain(v: Expr, range: RationalInterval, config: XConfig,
    uncertain: Rational, withRoundoff: Boolean, machineEps: Rational): (XFloat, Int) = {
    assert(uncertain >= Rational.zero)

    var (newError, index) = addNoiseWithIndex(new XRationalForm(Rational.zero), uncertain)

    if (withRoundoff) {
      val rndoff = roundoff(range + new RationalInterval(-uncertain, uncertain), machineEps)
      (new XFloat(v, range, addNoise(newError, rndoff), config, machineEps), index)
    } else {
      (new XFloat(v, range, newError, config, machineEps), index)
    }
  }

  def withIndex(v: Variable, range: RationalInterval, config: XConfig, machineEps: Rational): (XFloat, Int) = {
    val rndoff = roundoff(range, machineEps)
    val (newError, index) = addNoiseWithIndex(new XRationalForm(Rational.zero), rndoff)
    (new XFloat(v, range, newError, config, machineEps), index)
  }

  private def roundoff(range: RationalInterval, machineEps: Rational): Rational = {
    val maxAbs = max(abs(range.xlo), abs(range.xhi))
    // Without scaling this can return fractions with very large numbers
    // TODO: scale the result
    val simplifiedMax = Rational.scaleToIntsUp(maxAbs)
    return machineEps * simplifiedMax
  }

  private def roundoff(r: Rational, machineEps: Rational): Rational = {
    return machineEps * abs(r)
  }

  var verbose = false
}



class XFloat(val tr: Expr, val appInt: RationalInterval, val err: XRationalForm,
  val cnfg: XConfig, val machineEps: Rational) extends XReal(tr, appInt, err, cnfg) {
  import XFloat._

  
  /*def errorString(variables: Iterable[Int]): String = {
    val (varErrors, otherErrors): (Queue[Deviation], Queue[Deviation]) =
      error.noise.partition(
        d => d match { case v: VariableDev => true; case _ => false}
      )
    println("------------> ")
    println("varErrors: " + varErrors)
    println("otherErrors: " + otherErrors)
    "%s +/- %s +/- [%s]".format(error.x0, varErrors.toString, sumQueue(otherErrors))
  }*/

  override def unary_-(): XReal = {
    var (newTree, newRealRange, newError, newConfig) = super.negate
    new XFloat(newTree, newRealRange, newError, newConfig, machineEps)
  }

  override def +(y: XReal): XReal = {
    assert(y.getClass == this.getClass)
    assert(this.machineEps == y.asInstanceOf[XFloat].machineEps)
    if (verbose) println("+fl " + this + " to " + y)
    var (newTree, newRealRange, newError, newConfig) = super.add(y)
    val rndoff = roundoff(newRealRange + newError.interval)
    newError = addNoise(newError, rndoff)
    new XFloat(newTree, newRealRange, newError, newConfig, machineEps)
  }

  override def -(y: XReal): XReal = {
    assert(y.getClass == this.getClass)
    assert(this.machineEps == y.asInstanceOf[XFloat].machineEps)
    if (verbose) println("-fl " + this + " from " + y)
    var (newTree, newRealRange, newError, newConfig) = super.subtract(y)
    val rndoff = roundoff(newRealRange + newError.interval)
    newError = addNoise(newError, rndoff)
    return new XFloat(newTree, newRealRange, newError, newConfig, machineEps)
  }

  override def *(y: XReal): XReal = {
    assert(y.getClass == this.getClass)
    assert(this.machineEps == y.asInstanceOf[XFloat].machineEps)
    if (verbose) println("*fl " + this.tree + " with " + y.tree)
    if (verbose) println("x.error: " + this.error.longString)
    if (verbose) println("y.error: " + y.error.longString)
    var (newTree, newRealRange, newError, newConfig) = super.multiply(y)
    val rndoff = roundoff(newRealRange + newError.interval)

    newError = addNoise(newError, rndoff)
    new XFloat(newTree, newRealRange, newError, newConfig, machineEps)
  }

  override def /(y: XReal): XReal = {
    assert(y.getClass == this.getClass)
    assert(this.machineEps == y.asInstanceOf[XFloat].machineEps)
    if (verbose) println("/fl " + this.tree + " with " + y.tree)
    var (newTree, newRealRange, newError, newConfig) = super.divide(y)
    val rndoff = roundoff(newRealRange + newError.interval)
    newError = addNoise(newError, rndoff)
    new XFloat(newTree, newRealRange, newError, newConfig, machineEps)
  }

  override def squareRoot: XReal = {
    var (newTree, newRealRange, newError, newConfig) = super.takeSqrtRoot
    val rndoff = roundoff(newRealRange + newError.interval)
    newError = addNoise(newError, rndoff)
    new XFloat(newTree, newRealRange, newError, newConfig, machineEps)
  }

  override def toString: String =
    "%s -f (%.16g)(%s)".format(this.interval.toString, this.maxError.toDouble, tree)

  // Always returns a positive number
  private def roundoff(range: RationalInterval): Rational = {
    val maxAbs = max(abs(range.xlo), abs(range.xhi))
    // Without scaling this can return fractions with very large numbers
    // TODO: scale the result
    val simplifiedMax = Rational.scaleToIntsUp(maxAbs)
    return machineEps * simplifiedMax
  }

  private def roundoff(r: Rational): Rational = {
    return machineEps * abs(r)
  }

}
