package leon
package numerics

import purescala.Trees._

import ceres.common.{Rational, RationalInterval}
//import ceres.affine.{RationalForm}
import affine._
import Rational._
import XRationalForm._
import affine.Utils._

import collection.mutable.Queue
import java.math.{BigInteger, BigDecimal}

object XFloat {

  // double constant (we include rdoff error)
  def apply(d: Double, solver: NumericSolver): XFloat = {
    val r = rationalFromReal(d)
    val rndoff = roundoff(r)
    val newError = addNoise(new XRationalForm(Rational.zero), rndoff)
    return new XFloat(RationalLiteral(r), new XRationalForm(r), newError, solver)
  }

  // constant
  def apply(r: Rational, solver: NumericSolver): XFloat = {
    val newError = new XRationalForm(Rational.zero)
    return new XFloat(RationalLiteral(r), new XRationalForm(r), newError, solver)
  }

  // variable
  def apply(v: Variable, range: RationalInterval, solver: NumericSolver): XFloat = {
    val approx = XRationalForm(range)
    val rndoff = roundoff(range) // another version of that fnc?
    val newError = addNoise(new XRationalForm(Rational.zero), rndoff)
    return new XFloat(v, approx, newError, solver)
  }

  def withIndex(v: Variable, range: RationalInterval, solver: NumericSolver): (XFloat, Int) = {
    val approx = XRationalForm(range)
    val rndoff = roundoff(range) // another version of that fnc?
    val (newError, index) = addNoiseWithIndex(new XRationalForm(Rational.zero), rndoff)
    return (new XFloat(v, approx, newError, solver), index)
  }

  // Unit roundoff
  val u = Rational(new BigInt(new BigInteger("1")),
    new BigInt(new BigInteger("2")).pow(53))

  // Always returns a positive number
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
  A datatype for range arithmetic that keeps track of floating-point roundoff
  errors.
  The solver has to be "preconfigured" with the precondition including bounds
  on variables.
  NOTE: this means that once you popped the preconditions, you cannot get any
  useful bounds anymore.
  @param tree expression tree
  @param approxRange approximation of the real-valued range
  @param floating-point roundoff errors
  @param solver the Z3 solver used to determine precise real-valued ranges
 */
class XFloat(val tree: Expr, val approxRange: XRationalForm, val error: XRationalForm,
  solver: NumericSolver) {
  import XFloat._

  lazy val realInterval: RationalInterval = getTightInterval(tree, approxRange)

  lazy val interval: RationalInterval = realInterval + error.interval

  lazy val maxRoundoff: Rational = {
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

  def unary_-(): XFloat = new XFloat(UMinus(tree), -approxRange, -error, solver)

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
    return new XFloat(newTree, newApprox, newError, solver)
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
    return new XFloat(newTree, newApprox, newError, solver)
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
    return new XFloat(newTree, newApprox, newError, solver)
  }

  def /(y: XFloat): XFloat = {
    // TODO: catch division by zero

    //if (y.isExact) {
      

    // Compute approximation
    val tightInverse = getTightInterval(Division(FloatLiteral(1.0), y.tree), y.approxRange.inverse)
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
    return new XFloat(newTree, newApprox, newError, solver)
  }

  override def toString: String = this.interval.toString + " - (" +
    this.maxRoundoff + ")(abs)" 

  private def getTightInterval(tree: Expr, approx: XRationalForm): RationalInterval = {
    // Sanity check. If no scope is present, XFloat used without a precondition
    // hence this will fail, as we then have no bounds for variables
    assert(solver.getNumScopes > 0, "Trying to tighten interval but no scopes left!")

    //println("tightening: " + tree)
    val res = solver.tightenRange(tree, approx.interval)
    //println("tightening was successful")
    return res
  }
}
