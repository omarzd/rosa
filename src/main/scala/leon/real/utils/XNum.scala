/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package real

import purescala.Trees.{Expr, Variable}
import Precision.{roundoff, isExactInFloats}
import Rational._

object XNum {

  def records2xnums(records: Iterable[Record], precondition: Expr, additionalConstr: Set[Expr],
    withRoundoff: Boolean)(implicit precision: Precision): Map[Expr, XNum] = {

    records.map({
      case Record(id, lo, up, Some(absError), aId, _) =>
        (Variable(aId) -> XNum(Variable(id), RationalInterval(lo, up), precondition,
          additionalConstr, absError, withRoundoff))
      
      case rec @ Record(id, lo, up, None, aId, None) if (rec.isInteger) =>
        (Variable(aId) -> XNum(Variable(id), RationalInterval(lo, up), precondition,
          additionalConstr, zero, false))

      case Record(id, lo, up, None, aId, None) => 
        (Variable(aId) -> XNum(Variable(id), RationalInterval(lo, up), precondition,
          additionalConstr, zero, true))
    }).toMap
  }

  def records2xnumsExact(records: Iterable[Record], precondition: Expr,
    additionalConstr: Set[Expr])(implicit precision: Precision): Map[Expr, XNum] = {

    records.map({
      case Record(id, lo, up, _, aId, _) =>
        (Variable(aId) -> XNum(Variable(id), RationalInterval(lo, up), precondition,
          additionalConstr, zero, false))
      }).toMap
  }

  def records2xnumsActualExact(records: Iterable[Record], precondition: Expr, 
    additionalConstr: Set[Expr])(implicit precision: Precision): Map[Expr, XNum] = {

      records.map({
        case rec @ Record(id, lo, up, _, aId, _) if rec.isInteger =>
          (Variable(aId) -> XNum(Variable(id), RationalInterval(lo, up), precondition,
            additionalConstr, zero, false))

        case rec @ Record(id, lo, up, _, aId, _) =>
          (Variable(aId) -> XNum(Variable(id), RationalInterval(rec.loAct.get, rec.upAct.get),
            precondition, additionalConstr, zero, false))
        }).toMap
    }


  def apply(v: Expr, realRange: RationalInterval, precondition: Expr, 
    additionalConstr: Set[Expr], error: Rational, withRoundoff: Boolean)(
    implicit precision: Precision): XNum = {

    if (error == zero) {
      if (withRoundoff) {
        // roundoff only, TODO: fix the exactness check for fp
        if(realRange.isPointRange && isExactInFloats(realRange.xlo, precision)) {
          XNum(RealRange(v, realRange, Set(precondition), additionalConstr), new RationalForm(zero))
        } else {
          XNum(RealRange(v, realRange, Set(precondition), additionalConstr),
           new RationalForm(zero) :+ roundoff(realRange, precision))
        }

      } else {
        // exact
        XNum(RealRange(v, realRange, Set(precondition), additionalConstr), new RationalForm(zero))
      }
          
    } else {
      if (withRoundoff) {
        // roundoff and uncertainty
        val rndoff = roundoff(realRange + RationalInterval(-error, error), precision)
        XNum(RealRange(v, realRange, Set(precondition), additionalConstr),
          new RationalForm(zero) :+ error :+ rndoff)
      } else {
        // no roundoff, but uncertainty
        XNum(RealRange(v, realRange, Set(precondition), additionalConstr),
          new RationalForm(zero) :+ error)
      }
    }
  }

  def removeErrors(xnum: XNum): XNum = {
    XNum(xnum.realRange, new RationalForm(zero))
  }

  def replaceError(xnum: XNum, newError: Rational): XNum = {
    XNum(xnum.realRange, new RationalForm(newError))
  }
}

case class XNum(realRange: RealRange, error: RationalForm) {

  def addCondition(c: Expr): XNum = XNum(realRange.addCondition(c), error)
  def replace(fresh: Map[Expr, Expr]): XNum = 
    XNum(realRange.replace(fresh), error)
  def cleanConstraints: XNum = XNum(realRange.cleanConstraints, error)

  val interval: RationalInterval = realRange.interval + error.interval

  lazy val maxError: Rational = {
    val i = error.interval
    max(abs(i.xlo), abs(i.xhi))
  }

  def unary_-(): XNum = {
    XNum(-realRange, -error)
  }

  def +(that: XNum)(implicit precision: Precision): XNum = {
    // new real range
    val newReal = this.realRange + that.realRange
    
    // propagate existing errors
    val propErr = this.error + that.error

    // new error  (TODO: not quite correct for fp)
    val newErr = roundoff(newReal.interval + propErr.interval, precision)

    XNum(newReal, propErr :+ newErr)
  }

  def -(that: XNum)(implicit precision: Precision): XNum = {
    val newReal = this.realRange - that.realRange
    val propErr = this.error - that.error
    val newErr = roundoff(newReal.interval + propErr.interval, precision)
    XNum(newReal, propErr :+ newErr)
  }

  def *(that: XNum)(implicit precision: Precision): XNum = {
    // new real range
    val newReal = this.realRange * that.realRange

    // propagated existing errors
    val propErr =
      RationalForm(this.realRange.interval) * that.error +
      RationalForm(that.realRange.interval) * this.error +
      this.error * that.error

    // new error
    val newErr = roundoff(newReal.interval + propErr.interval, precision)
    XNum(newReal, propErr :+ newErr)
  }

  // computed as x * 1/y 
  def /(that: XNum)(implicit precision: Precision): XNum = {
    
    // new real range
    val newReal = this.realRange / that.realRange

    // propagated existing errors
    val a = min(abs(that.realRange.interval.xlo), abs(that.realRange.interval.xhi))
    val errorMultiplier = -one / (a * a)
    val invErr = that.error * new RationalForm(errorMultiplier)

    val invRange = that.realRange.inverse

    val propErr = 
      RationalForm(this.realRange.interval) * invErr +
      RationalForm(invRange.interval) * this.error +
      this.error * invErr

    // new roundoff
    val newErr = roundoff(newReal.interval + propErr.interval, precision)
    XNum(newReal, propErr :+ newErr)
  }

  def squareRoot(implicit precision: Precision): XNum = precision match {
    case FPPrecision(_) => throw UnsupportedRealFragmentException("Sqrt not supported for fixed-points.")

    case _ =>
      // new real range
      val newReal = this.realRange.squareRoot


      // propagated existing errors
      val a = min(abs(this.realRange.interval.xlo), abs(this.realRange.interval.xhi))
      val errorMultiplier = Rational(1L, 2L) / sqrtDown(a)
      val propErr = this.error * new RationalForm(errorMultiplier)

      // new roundoff
      val newErr = roundoff(newReal.interval + propErr.interval, precision)
      XNum(newReal, propErr :+ newErr)
  }

}