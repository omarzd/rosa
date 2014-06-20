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
import Precision._

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
  def variables2xfloats(vars: Iterable[Record], config: XConfig, precision: Precision, withRoundoff: Boolean = false): (Map[Expr, XFloat], Map[Int, Expr]) = {
    var variableMap: Map[Expr, XFloat] = Map.empty
    var indexMap: Map[Int, Expr] = Map.empty

    for(rec <- vars) {
      rec match {
        case r @ Record(id, lo, up, Some(absError), aId, _) =>
          val (xfloat, index) = XFloat.xFloatWithUncertain(Variable(id), RationalInterval(lo, up), config,
            absError, withRoundoff, precision)
          variableMap = variableMap + (Variable(aId) -> xfloat)
          indexMap = indexMap + (index -> Variable(aId))

        case Record(id, lo, up, None, aId, None) =>
          val (xfloat, index) = XFloat.xFloatWithRoundoff(Variable(id), RationalInterval(lo, up), config, precision)
          variableMap = variableMap + (Variable(aId) -> xfloat)
          indexMap = indexMap + (index -> Variable(aId))

        case _ =>
          throw new Exception("bug!")
      }
    }
    (variableMap, indexMap)
  }

  def variables2xfloatsExact(vars: Iterable[Record], config: XConfig, precision: Precision): Map[Expr, XFloat] = {
    var variableMap: Map[Expr, XFloat] = Map.empty
    
    for(rec <- vars) {
      rec match {

        case Record(id, lo, up, _, aId, _) =>
          val xfloat = XFloat.xFloatExact(Variable(id), RationalInterval(lo, up), config, precision)
          variableMap = variableMap + (Variable(aId) -> xfloat)

        case _ =>
          throw new Exception("bug!")
      }
    }
    variableMap
  }

  def variables2xfloatsActualExact(vars: Iterable[Record], config: XConfig, precision: Precision): Map[Expr, XFloat] = {
    var variableMap: Map[Expr, XFloat] = Map.empty
    //println("actual xfloats")
    for(rec <- vars) {
      rec match {
        case Record(id, lo, up, _, aId, _) if rec.isInteger =>
          val xfloat = XFloat.xFloatExact(Variable(id), RationalInterval(lo, up), config, precision)
          variableMap = variableMap + (Variable(aId) -> xfloat)


        case Record(id, lo, up, _, aId, _) =>
          val xfloat = XFloat.xFloatExact(Variable(id), RationalInterval(rec.loAct.get, rec.upAct.get), config, precision)
          variableMap = variableMap + (Variable(aId) -> xfloat)

        case _ =>
          throw new Exception("bug!")
      }
    }
    variableMap
  }


  // double constant (we include rdoff error)
  def apply(d: Double, config: XConfig, precision: Precision): XFloat = {
    val rndoff = roundoff(d, precision)
    val r = rationalFromReal(d)
    //val rndoff = roundoff(r, machineEps)
    val newError = addNoise(new XRationalForm(Rational.zero), rndoff)
    new XFloat(RealLiteral(r), RationalInterval(r, r), newError, config, precision)
  }

  // constant
  def apply(r: Rational, config: XConfig, precision: Precision): XFloat = {
    val newError =  if (Precision.isExactInFloats(r)) {
      new XRationalForm(Rational.zero)
    } else {
      addNoise(new XRationalForm(Rational.zero), roundoff(r, precision))
    }
    new XFloat(RealLiteral(r), RationalInterval(r,r), newError, config, precision)
  }

  /**
    Creates an XFloat and adds the max roundoff error over the range automatically.
    @param v variable associated with this XFloat
    @param range real-valued range of this XFloat
    @param config solver, precondition, which precision to choose
  **/
  def xFloatWithRoundoff(v: Variable, range: RationalInterval, config: XConfig, precision: Precision): (XFloat, Int) = {
    // For when the specs say 3 <= x && x <= 3
    if (range.isPointRange && isExactInFloats(range.xlo)) {
      (new XFloat(v, range, new XRationalForm(Rational.zero), config, precision), -1)
    } else {
      val rndoff = roundoff(range, precision)
      val (newError, index) = addNoiseWithIndex(new XRationalForm(Rational.zero), rndoff)
      (new XFloat(v, range, newError, config, precision), index)
    }

    
  }

  /**
    Creates an XFloat and adds the max roundoff error over the range automatically.
    @param v variable associated with this XFloat
    @param range real-valued range of this XFloat
    @param config solver, precondition, which precision to choose
  **/
  def xFloatExact(v: Variable, range: RationalInterval, config: XConfig, precision: Precision): XFloat = {
    new XFloat(v, range, new XRationalForm(Rational.zero), config, precision)
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
    uncertain: Rational, withRoundoff: Boolean, precision: Precision): (XFloat, Int) = {
    assert(uncertain >= Rational.zero)

    var (newError, index) = addNoiseWithIndex(new XRationalForm(Rational.zero), uncertain)

    if (withRoundoff) {
      val rndoff = roundoff(range + new RationalInterval(-uncertain, uncertain), precision)
      (new XFloat(v, range, addNoise(newError, rndoff), config, precision), index)
    } else {
      (new XFloat(v, range, newError, config, precision), index)
    }
  }

  def withIndex(v: Variable, range: RationalInterval, config: XConfig, precision: Precision): (XFloat, Int) = {
    val rndoff = roundoff(range, precision)
    val (newError, index) = addNoiseWithIndex(new XRationalForm(Rational.zero), rndoff)
    (new XFloat(v, range, newError, config, precision), index)
  }

  var verbose = false
}



class XFloat(val tr: Expr, val appInt: RationalInterval, val err: XRationalForm,
  val cnfg: XConfig, val precision: Precision) extends XReal(tr, appInt, err, cnfg) {
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

  override def cleanConfig: XReal = {
    new XFloat(tree, approxInterval, error, getCleanConfig, precision)
  }

  override def unary_-(): XReal = {
    var (newTree, newRealRange, newError, newConfig) = super.negate
    new XFloat(newTree, newRealRange, newError, newConfig, precision)
  }

  override def +(y: XReal): XReal = {
    assert(y.getClass == this.getClass)
    assert(this.precision == y.asInstanceOf[XFloat].precision)
    if (verbose) println("+fl " + this + " to " + y)
    var (newTree, newRealRange, newError, newConfig) = super.add(y)
    val rndoff = roundoff(newRealRange + newError.interval, precision)
    newError = addNoise(newError, rndoff)
    new XFloat(newTree, newRealRange, newError, newConfig, precision)
  }

  override def -(y: XReal): XReal = {
    assert(y.getClass == this.getClass)
    assert(this.precision == y.asInstanceOf[XFloat].precision)
    if (verbose) println("-fl " + this + " from " + y)
    var (newTree, newRealRange, newError, newConfig) = super.subtract(y)
    val rndoff = roundoff(newRealRange + newError.interval, precision)
    newError = addNoise(newError, rndoff)
    new XFloat(newTree, newRealRange, newError, newConfig, precision)
  }

  override def *(y: XReal): XReal = {
    assert(y.getClass == this.getClass)
    assert(this.precision == y.asInstanceOf[XFloat].precision)
    if (verbose) println("*fl " + this.tree + " with " + y.tree)
    if (verbose) println("x.error: " + this.error.longString)
    if (verbose) println("y.error: " + y.error.longString)
    var (newTree, newRealRange, newError, newConfig) = super.multiply(y)
    val rndoff = roundoff(newRealRange + newError.interval, precision)
    newError = addNoise(newError, rndoff)
    new XFloat(newTree, newRealRange, newError, newConfig, precision)
  }

  override def /(y: XReal): XReal = {
    assert(y.getClass == this.getClass)
    assert(this.precision == y.asInstanceOf[XFloat].precision)
    if (verbose) println("/fl " + this.tree + " with " + y.tree)
    var (newTree, newRealRange, newError, newConfig) = super.divide(y)
    val rndoff = roundoff(newRealRange + newError.interval, precision)
    newError = addNoise(newError, rndoff)
    new XFloat(newTree, newRealRange, newError, newConfig, precision)
  }

  override def squareRoot: XReal = {
    var (newTree, newRealRange, newError, newConfig) = super.takeSqrtRoot
    val rndoff = roundoff(newRealRange + newError.interval, precision)
    newError = addNoise(newError, rndoff)
    new XFloat(newTree, newRealRange, newError, newConfig, precision)
  }

  override def toString: String =
    "%s -f (%.16g)(%s)".format(this.interval.toString, this.maxError.toDouble, tree)

  // Always returns a positive number
  /*private def roundoff(range: RationalInterval): Rational = {
    val maxAbs = max(abs(range.xlo), abs(range.xhi))
    // Without scaling this can return fractions with very large numbers
    // TODO: try scaling the result
    val simplifiedMax = Rational.scaleToIntsUp(maxAbs)
    machineEps * simplifiedMax
  }

  private def roundoff(r: Rational): Rational = {
    machineEps * abs(r)
  }*/

}
