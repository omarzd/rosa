package leon
package numerics
package affine

import purescala.Trees._

import Rational._
import XRationalForm._
import affine.Utils._
import Precision._
import numerics.Utils._
import VariableShop._

import collection.mutable.Queue
import java.math.{BigInteger, BigDecimal}

object XFloat {

  /**
    Converts variable-record pairs into XFloats.
    Discards all variables for which neither rndoff nor noise has been specified.
    @param vars what we want to convert
    @param config solver, precondition, which precision to choose
    @param withRoundoff whether the initial XFloat should also get an roundoff error, additionally to the noise
   */
  def variables2xfloats(vars: Map[Variable, Record], config: XFloatConfig, withRoundoff: Boolean = true):
    (Map[Expr, XFloat], Map[Int, Expr]) = {
    var variableMap: Map[Expr, XFloat] = Map.empty
    var indexMap: Map[Int, Expr] = Map.empty

    for((k, rec) <- vars) {
      if (rec.isComplete) {
        (rec.absNoise, rec.relNoise) match { // was already checked that only one is possible
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
        }

      }
    }
    (variableMap, indexMap)
  }


  // double constant (we include rdoff error)
  def apply(d: Double, config: XFloatConfig): XFloat = {
    val r = rationalFromReal(d)
    val rndoff = roundoff(r, config.machineEps)
    val newError = addNoise(new XRationalForm(Rational.zero), rndoff)
    return new XFloat(RationalLiteral(r), RationalInterval(r, r), newError, config)
  }

  // constant
  def apply(r: Rational, config: XFloatConfig): XFloat = {
    val newError = new XRationalForm(Rational.zero)
    return new XFloat(RationalLiteral(r), RationalInterval(r,r), newError, config)
  }

  /**
    Creates an XFloat and adds the max roundoff error over the range automatically.
    @param v variable associated with this XFloat
    @param range real-valued range of this XFloat
    @param config solver, precondition, which precision to choose
  **/
  def xFloatWithRoundoff(v: Variable, range: RationalInterval, config: XFloatConfig): (XFloat, Int) = {
    val rndoff = roundoff(range, config.machineEps)
    val (newError, index) = addNoiseWithIndex(new XRationalForm(Rational.zero), rndoff)
    return (new XFloat(v, range, newError, config), index)
  }

  /**
    Creates an XFloat with a given uncertainty.
    @param v variable associated with this XFloat
    @param range real-valued range of this XFloat
    @param solver solver, precondition, which precision to choose
    @param uncertain max uncertainty
    @param withRoundoff if true an additional roundoff error will be added automatically, additionally to noise
  **/
  def xFloatWithUncertain(v: Expr, range: RationalInterval, config: XFloatConfig,
    uncertain: Rational, withRoundoff: Boolean): (XFloat, Int) = {
    assert(uncertain >= Rational.zero)

    var (newError, index) = addNoiseWithIndex(new XRationalForm(Rational.zero), uncertain)

    if (withRoundoff) {
      val rndoff = roundoff(range + new RationalInterval(-uncertain, uncertain), config.machineEps)
      return (new XFloat(v, range, addNoise(newError, rndoff), config), index)
    } else {
      return (new XFloat(v, range, newError, config), index)
    }
  }

  def withIndex(v: Variable, range: RationalInterval, config: XFloatConfig): (XFloat, Int) = {
    val rndoff = roundoff(range, config.machineEps)
    val (newError, index) = addNoiseWithIndex(new XRationalForm(Rational.zero), rndoff)
    return (new XFloat(v, range, newError, config), index)
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

  val verbose = false
  // TODO: alright, this is not exact
  val MaxDouble = Rational(Double.MaxValue)
  val MaxFloat = Rational(Float.MaxValue)

}


/**
  A datatype for range arithmetic that keeps track of floating-point roundoff errors.
  @param tree expression tree
  @param approxRange approximation of the real-valued range
  @param error various uncertainties, incl. roundoffs
  @param config solver, precondition, which precision to choose
 */
class XFloat(val tree: Expr, val approxInterval: RationalInterval, val error: XRationalForm, val config: XFloatConfig) {
  import XFloat._

  lazy val realInterval: RationalInterval = {
    getTightInterval(tree, approxInterval, config.getCondition)
  }
  lazy val interval: RationalInterval = realInterval + error.interval

  lazy val maxError: Rational = {
    val i = error.interval
    max(abs(i.xlo), abs(i.xhi))
  }

  // Check for potential overflow
  config.precision match {
    case Float32 =>
      if (interval.xlo < -MaxFloat || MaxFloat < interval.xhi) {
        config.reporter.warning("Potential overflow detected for: %s,\nwith precondition %s".format(tree, config.precondition))
      }
    case Float64 =>
      if (interval.xlo < -MaxDouble || MaxDouble < interval.xhi) {
        config.reporter.warning("Potential overflow detected for: %s,\nwith precondition %s".format(tree, config.precondition))
        config.reporter.info(interval)
      }
    case DoubleDouble => // same range as Double
      if (interval.xlo < -MaxDouble || MaxDouble < interval.xhi) {
        config.reporter.warning("Potential overflow detected for: %s,\nwith precondition %s".format(tree, config.precondition))
        config.reporter.info(interval)
      }
    case QuadDouble => // same range as Double
      if (interval.xlo < -MaxDouble || MaxDouble < interval.xhi) {
        config.reporter.warning("Potential overflow detected for: %s,\nwith precondition %s".format(tree, config.precondition))
        config.reporter.info(interval)
      }
  }

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

  def unary_-(): XFloat = new XFloat(UMinus(tree), -approxInterval, -error, config)

  def +(y: XFloat): XFloat = {
    if (verbose) println("Adding " + this + " to " + y)
    val newConfig = config.and(y.config)
    val newTree = Plus(this.tree, y.tree)
    val newInterval = this.approxInterval + y.approxInterval

    var newError = this.error + y.error
    val newRealRange = getTightInterval(newTree, newInterval, newConfig.getCondition)
    val rndoff = roundoff(newRealRange + newError.interval)
    newError = addNoise(newError, rndoff)

    return new XFloat(newTree, newRealRange, newError, newConfig)
  }

  def -(y: XFloat): XFloat = {
    if (verbose) println("Subtracting " + this + " from " + y)
    val newConfig = config.and(y.config)
    val newTree = Minus(this.tree, y.tree)
    val newInterval = this.approxInterval - y.approxInterval

    var newError = this.error - y.error
    val newRealRange = getTightInterval(newTree, newInterval, newConfig.getCondition)
    val rndoff = roundoff(newRealRange + newError.interval)
    newError = addNoise(newError, rndoff)
    return new XFloat(newTree, newRealRange, newError, newConfig)
  }

  def *(y: XFloat): XFloat = {
    if (verbose) println("Mult " + this.tree + " with " + y.tree)
    if (verbose) println("x.error: " + this.error.longString)
    if (verbose) println("y.error: " + y.error.longString)
    val newConfig = config.and(y.config)
    val newTree = Times(this.tree, y.tree)
    val newInterval = this.approxInterval * y.approxInterval

    val xAA = XRationalForm(this.realInterval)
    val yAA = XRationalForm(y.realInterval)
    val yErr = y.error
    val xErr = this.error

    var newError = xAA*yErr + yAA*xErr + xErr*yErr
    val newRealRange = getTightInterval(newTree, newInterval, newConfig.getCondition)
    val rndoff = roundoff(newRealRange + newError.interval)

    //One could also keep track of the input dependencies from xAA and yAA
    // which may be larger than the nonlinear stuff
    newError = addNoise(newError, rndoff)
    return new XFloat(newTree, newRealRange, newError, newConfig)
  }

  def /(y: XFloat): XFloat = {
    if (y.interval.xlo < Rational.zero && y.interval.xhi > Rational.zero) {
      config.reporter.warning("Potential division by zero detected for: %s/%s,\nwith precondition %s".format(
        this.tree, y.tree, config.precondition))
      config.reporter.warning("y.interval: " + y.interval)
    }

    //if (y.isExact) {


    // Compute approximation
    //val tightInverse = getTightInterval(Division(new RationalLiteral(1), y.tree), y.approxRange.inverse)
    val tightInverse = getTightInterval(Division(new RationalLiteral(1), y.tree), RationalInterval(one, one)/y.approxInterval, y.config.getCondition)
    val kAA = XRationalForm(tightInverse)
    val xAA = XRationalForm(this.realInterval)
    val xErr = this.error

    val yInt = y.interval
    val a = min(abs(yInt.xlo), abs(yInt.xhi))
    val errorMultiplier = -one / (a*a)
    val gErr = y.error * new XRationalForm(errorMultiplier)

    // Now do the multiplication x * (1/y)
    val newConfig = config.and(y.config)
    val newTree = Division(this.tree, y.tree)
    val newInterval = this.approxInterval / y.approxInterval


    var newError = xAA*gErr + kAA*xErr + xErr*gErr
    val newRealRange = getTightInterval(newTree, newInterval, newConfig.getCondition)
    val rndoff = roundoff(newRealRange + newError.interval)

    newError = addNoise(newError, rndoff)
    return new XFloat(newTree, newRealRange, newError, newConfig)
  }

  def squareRoot: XFloat = {
    if (interval.xlo < Rational.zero || interval.xhi < Rational.zero) {
      config.reporter.warning("Potential square root of a negative number for: %s,\nwith precondition %s".format(
        this.tree, config.precondition))
      config.reporter.warning("interval: " + this.interval)
    }
    // if this.isExact

    val int = this.interval
    val a = min(abs(int.xlo), abs(int.xhi))
    val errorMultiplier = Rational(1l, 2l) / sqrtDown(a)

    //val newTree = Sqrt(this.tree)
    val (sqrtVar, n) = getNewSqrtVariablePair
    val newTree = sqrtVar
    val newCondition = And(Equals(Times(sqrtVar, sqrtVar), this.tree), LessEquals(RationalLiteral(zero), sqrtVar))
    val newConfig = config.addCondition(newCondition)

    val newInterval = RationalInterval(sqrtDown(this.approxInterval.xlo), sqrtUp(this.approxInterval.xhi))

    var newError = this.error * new XRationalForm(errorMultiplier)
    val newRealRange = getTightInterval(newTree, newInterval, newConfig.getCondition)
    val rndoff = roundoff(newRealRange + newError.interval)
    newError = addNoise(newError, rndoff)

    return new XFloat(newTree, newRealRange, newError, newConfig)
  }


  override def toString: String =
    "%s - (%.16g)(%s)".format(this.interval.toString, this.maxError.toDouble, tree)

  // Always returns a positive number
  private def roundoff(range: RationalInterval): Rational = {
    val maxAbs = max(abs(range.xlo), abs(range.xhi))
    // Without scaling this can return fractions with very large numbers
    // TODO: scale the result
    val simplifiedMax = Rational.scaleToIntsUp(maxAbs)
    return config.machineEps * simplifiedMax
  }

  private def roundoff(r: Rational): Rational = {
    return config.machineEps * abs(r)
  }

  private def getTightInterval(tree: Expr, approx: RationalInterval, condition: Expr): RationalInterval = {
    //println("\n tightening: " + tree)
    //println("with pre: " + condition)
    val massagedTree = ArithmeticOps.totalMakeover(tree)
    //println("massaged: " + massagedTree)
    //println("initial approx: " + approx)

    val res = config.solver.tightenRange(massagedTree, condition, approx, config.solverMaxIter, config.solverPrecision)
    //println(tree + "  " + config.solverMaxIter)
    //val res = approx
    //println("after tightening: " + res)

    return res
  }
}
