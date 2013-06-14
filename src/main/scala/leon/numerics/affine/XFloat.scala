package leon
package numerics
package affine

import purescala.Trees._

import ceres.common.{Rational, RationalInterval}
import affine._
import Rational._
import XRationalForm._
import affine.Utils._

import collection.mutable.Queue
import java.math.{BigInteger, BigDecimal}

object XFloat {

  // TODO: XFloat should also be parametric in the floating-point precision
  // TODO: this does not add an XFloat if neither rndoff nor noise has been specified
  def variables2xfloats(vars: Map[Variable, Record], solver: NumericSolver, pre: Expr, withRoundoff: Boolean = true):
    (Map[Expr, XFloat], Map[Expr, Int]) = {
    var variableMap: Map[Expr, XFloat] = Map.empty
    var indexMap: Map[Expr, Int] = Map.empty

    for((k, rec) <- vars) {
      if (rec.isComplete) {
        rec.rndoff match {
          case Some(true) =>
            val (xfloat, index) = XFloat.xFloatWithRoundoff(k,
                    RationalInterval(rec.lo.get, rec.up.get),
                    solver, pre)
            variableMap = variableMap + (k -> xfloat)
            indexMap = indexMap + (k -> index)

          case None =>
            // index is the index of the main uncertainty, not the roundoff
            val (xfloat, index) = XFloat.xFloatWithUncertain(k,
                    RationalInterval(rec.lo.get, rec.up.get),
                    solver, pre,
                    rec.noise.get, withRoundoff)
            variableMap = variableMap + (k -> xfloat)
            indexMap = indexMap + (k -> index)
        }
      }
    }
    (variableMap, indexMap)
  }


  // double constant (we include rdoff error)
  def apply(d: Double, solver: NumericSolver, pre: Expr): XFloat = {
    val r = rationalFromReal(d)
    val rndoff = roundoff(r)
    val newError = addNoise(new XRationalForm(Rational.zero), rndoff)
    return new XFloat(RationalLiteral(r), new XRationalForm(r), newError, solver, pre)
  }

  // constant
  def apply(r: Rational, solver: NumericSolver, pre: Expr): XFloat = {
    val newError = new XRationalForm(Rational.zero)
    return new XFloat(RationalLiteral(r), new XRationalForm(r), newError, solver, pre)
  }

  /**
    Creates an XFloat and adds the max roundoff error over the range automatically.
    @param v variable associated with this XFloat
    @param range real-valued range of this XFloat
    @param solver Z3 backed solver to use for range tightening
  **/
  def xFloatWithRoundoff(v: Variable, range: RationalInterval, solver: NumericSolver, pre: Expr): (XFloat, Int) = {
    val approx = XRationalForm(range)
    val rndoff = roundoff(range) // another version of that fnc?
    val (newError, index) = addNoiseWithIndex(new XRationalForm(Rational.zero), rndoff)
    return (new XFloat(v, approx, newError, solver, pre), index)
  }

  /**
    Creates an XFloat with a given uncertainty.
    @param v variable associated with this XFloat
    @param range real-valued range of this XFloat
    @param solver Z3 backed solver to use for range tightening
    @param uncertain max uncertainty
    @param withRoundoff if true an additional roundoff error will be added automatically
  **/
  def xFloatWithUncertain(v: Variable, range: RationalInterval, solver: NumericSolver,
    pre: Expr, uncertain: Rational, withRoundoff: Boolean): (XFloat, Int) = {
    assert(uncertain >= Rational.zero)

    val approx = XRationalForm(range)
    var (newError, index) = addNoiseWithIndex(new XRationalForm(Rational.zero), uncertain)

    if (withRoundoff) {
      val rndoff = roundoff(range + new RationalInterval(-uncertain, uncertain)) // another version of that fnc?
      return (new XFloat(v, approx, addNoise(newError, rndoff), solver, pre), index)
    } else {
      return (new XFloat(v, approx, newError, solver, pre), index)
    }
  }

  def withIndex(v: Variable, range: RationalInterval, solver: NumericSolver, pre: Expr): (XFloat, Int) = {
    val approx = XRationalForm(range)
    val rndoff = roundoff(range) // another version of that fnc?
    val (newError, index) = addNoiseWithIndex(new XRationalForm(Rational.zero), rndoff)
    return (new XFloat(v, approx, newError, solver, pre), index)
  }

  // Unit roundoff
  val u = numerics.unitRndoff// Rational(new BigInt(new BigInteger("1")),
    //new BigInt(new BigInteger("2")).pow(53))

  // Always returns a positive number
  // TODO: in order to make this parametric wrt to roundoff, we could pass aorund this function
  def roundoff(range: RationalInterval): Rational = {
    val maxAbs = max(abs(range.xlo), abs(range.xhi))
    // Without scaling this can return fractions with very large numbers
    // TODO: scale the result
    val simplifiedMax = Rational.scaleToIntsUp(maxAbs)
    return u * simplifiedMax
  }

  def roundoff(r: Rational): Rational = {
    return u * abs(r)
  }

  val verbose = false

}

/**
  A datatype for range arithmetic that keeps track of floating-point roundoff errors.
  @param tree expression tree
  @param approxRange approximation of the real-valued range
  @param floating-point roundoff errors
  @param solver the Z3 solver used to determine precise real-valued ranges
 */
class XFloat(val tree: Expr, val approxRange: XRationalForm, val error: XRationalForm,
  solver: NumericSolver, precondition: Expr) {
  import XFloat._

  lazy val realInterval: RationalInterval = {
    getTightInterval(tree, approxRange)
  }
  lazy val interval: RationalInterval = realInterval + error.interval

  lazy val maxError: Rational = {
    val i = error.interval
    max(abs(i.xlo), abs(i.xhi))
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

  def unary_-(): XFloat = new XFloat(UMinus(tree), -approxRange, -error, solver, precondition)

  // To be 100% correct, there is also a contribution from the old errors, (this.error + y.error) * \delta^2
  def +(y: XFloat): XFloat = {
    if (verbose) println("Adding " + this + " to " + y)
    val newTree = Plus(this.tree, y.tree)
    val newApprox = this.approxRange + y.approxRange

    var newError = this.error + y.error
    val newRange = getTightInterval(newTree, newApprox) + newError.interval
    val rndoff = roundoff(newRange)
    newError = addNoise(newError, rndoff)

    if(verbose) println("\naddition, newRange: " + newRange + "\n roundoff: " + rndoff)
    return new XFloat(newTree, newApprox, newError, solver, precondition)
  }

  def -(y: XFloat): XFloat = {
    if (verbose) println("Subtracting " + this + " from " + y)
    val newTree = Minus(this.tree, y.tree)
    val newApprox = this.approxRange - y.approxRange

    var newError = this.error - y.error
    val newRange = getTightInterval(newTree, newApprox) + newError.interval
    val rndoff = roundoff(newRange)
    newError = addNoise(newError, rndoff)
    if(verbose) println("\nsubtraction, newRange: " + newRange + "\n roundoff: " + rndoff)
    return new XFloat(newTree, newApprox, newError, solver, precondition)
  }

  def *(y: XFloat): XFloat = {
    if (verbose) println("Mult " + this.tree + " with " + y.tree)
    if (verbose) println("x.error: " + this.error.longString)
    if (verbose) println("y.error: " + y.error.longString)
    val newTree = Times(this.tree, y.tree)
    val newApprox = this.approxRange * y.approxRange

    val xAA = XRationalForm(this.realInterval)
    val yAA = XRationalForm(y.realInterval)
    val yErr = y.error
    val xErr = this.error

    var newError = xAA*yErr + yAA*xErr + xErr*yErr
    val newRange = getTightInterval(newTree, newApprox) + newError.interval
    val rndoff = roundoff(newRange)

    //One could also keep track of the input dependencies from xAA and yAA
    // which may be larger than the nonlinear stuff
    newError = addNoise(newError, rndoff)
    if (verbose) println("\nmultiplication, newRange: " + newRange + "\n roundoff: " + rndoff)
    if (verbose) println("new error: " + newError.longString)
    return new XFloat(newTree, newApprox, newError, solver, precondition)
  }

  def /(y: XFloat): XFloat = {
    // TODO: catch division by zero

    //if (y.isExact) {


    // Compute approximation
    val tightInverse = getTightInterval(Division(new RationalLiteral(1), y.tree), y.approxRange.inverse)
    val kAA = XRationalForm(tightInverse)
    val xAA = XRationalForm(this.realInterval)
    val xErr = this.error

    val yInt = y.interval
    val a = min(abs(yInt.xlo), abs(yInt.xhi))
    val errorMultiplier = negOne / (a*a)
    val gErr = y.error * new XRationalForm(errorMultiplier)

    // Now do the multiplication x * (1/y)
    val newTree = Division(this.tree, y.tree)
    val newApprox = this.approxRange / y.approxRange

    var newError = xAA*gErr + kAA*xErr + xErr*gErr
    val newRange = getTightInterval(newTree, newApprox) + newError.interval
    val rndoff = roundoff(newRange)

    newError = addNoise(newError, rndoff)
    if(verbose) println("\ndivision, newRange: " + newRange)
    if(verbose) println("            roundoff: " + rndoff)
    return new XFloat(newTree, newApprox, newError, solver, precondition)
  }

  // In fact, this is simpler than division
  def squareRoot: XFloat = {
    // TODO: catch sqrt of negative number

    // if this.isExact

    val int = this.interval
    // TODO: method on RationalInterval
    val a = min(abs(int.xlo), abs(int.xhi))
    val errorMultiplier = Rational(1l, 2l) / sqrtDown(a)

    val newTree = Sqrt(this.tree)
    val newApprox = this.approxRange.squareRoot

    var newError = this.error * new XRationalForm(errorMultiplier)
    val newRange = getTightInterval(newTree, newApprox) + newError.interval
    val rndoff = roundoff(newRange)
    newError = addNoise(newError, rndoff)

    return new XFloat(newTree, newApprox, newError, solver, precondition)
  }


  override def toString: String = this.interval.toString + " - (" +
    this.maxError + ")(abs)"

  private def getTightInterval(tree: Expr, approx: XRationalForm): RationalInterval = {
    //println("tightening: " + tree)
    //println(approx.interval)

    val res = solver.tightenRange(tree, precondition, approx.interval)
    //val res = approx.interval
    //println("tightening was successful")
    return res
  }
}
