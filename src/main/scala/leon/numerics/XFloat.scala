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
  def apply(d: Double, solver: NumericSolver): XFloat = {
    val r = rationalFromReal(d)
    val rndoff = roundoff(r)
    val newError = addNoise(new RationalForm(Rational.zero), rndoff)
    return new XFloat(RationalLiteral(r), new RationalForm(r), newError, solver)
  }

  // constant
  def apply(r: Rational, solver: NumericSolver): XFloat = {
    val newError = new RationalForm(Rational.zero)
    return new XFloat(RationalLiteral(r), new RationalForm(r), newError, solver)
  }

  // variable
  def apply(v: Variable, range: RationalInterval, solver: NumericSolver): XFloat = {
    val approx = RationalForm(range)
    val rndoff = roundoff(range) // another version of that fnc?
    val newError = addNoise(new RationalForm(Rational.zero), rndoff)
    return new XFloat(v, approx, newError, solver)
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

/**
  A datatype for range arithmetic that keeps track of floating-point roundoff
  errors.
  The solver has to be "preconfigured" with the precondition including bounds
  on variables.
  @param tree expression tree
  @param approxRange approximation of the real-valued range
  @param floating-point roundoff errors
  @param solver the Z3 solver used to determine precise real-valued ranges
 */
class XFloat(val tree: Expr, val approxRange: RationalForm, val error: RationalForm,
  solver: NumericSolver) {
  import XFloat._

  def interval: RationalInterval = {
    realInterval + error.interval
  }

  // TODO: cache this
  def realInterval: RationalInterval = {
    getTightInterval(tree, approxRange) 
  }

  def maxRoundoff: Rational = {
    val i = error.interval
    return max(abs(i.xlo), abs(i.xhi))
  }

  def unary_-(): XFloat = new XFloat(FUMinus(tree), -approxRange, -error, solver)

  //i.e. compute new real range, propagate errors, add new roundoff
  // To be 100% correct, there is also a contribution from the old errors,
  // (this.error + y.error) * \delta^2
  def +(y: XFloat): XFloat = {
    val newTree = FPlus(this.tree, y.tree)
    val newApprox = this.approxRange + y.approxRange

    val newRange = getTightInterval(newTree, newApprox)
    val rndoff = roundoff(newRange)
    val newError = addNoise(this.error + y.error, rndoff)
    if(verbose) println("\naddition, newRange: " + newRange)
    if(verbose) println("            roundoff: " + rndoff)
    return new XFloat(newTree, newApprox, newError, solver)
  }

  def -(y: XFloat): XFloat = {
    val newTree = FMinus(this.tree, y.tree)
    val newApprox = this.approxRange - y.approxRange

    val newRange = getTightInterval(newTree, newApprox)
    val rndoff = roundoff(newRange)
    val newError = addNoise(this.error - y.error, rndoff)
    if(verbose) println("\nsubtraction, newRange: " + newRange)
    if(verbose) println("               roundoff: " + rndoff)
    return new XFloat(newTree, newApprox, newError, solver)
  }

  def *(y: XFloat): XFloat = {
    val newTree = FTimes(this.tree, y.tree)
    val newApprox = this.approxRange * y.approxRange

    val newRange = getTightInterval(newTree, newApprox)
    val rndoff = roundoff(newRange)
    
    val xAA = RationalForm(this.realInterval)
    val yAA = RationalForm(y.realInterval)
    val yErr = y.error
    val xErr = this.error
    val newError = addNoise(xAA*yErr + yAA*xErr + xErr*yErr, rndoff)
    if (verbose) println("multiplication: " + this.tree + "  *  " + y.tree)
    if(verbose) println("\nmultiplication, newRange: " + newRange)
    if(verbose) println("                  roundoff: " + rndoff)
    return new XFloat(newTree, newApprox, newError, solver)
  }

  def /(y: XFloat): XFloat = {
    // TODO: catch division by zero

    //if (y.isExact) {
      

    // Compute approximation
    val tightInverse = getTightInterval(FDivision(IntLiteral(1), y.tree), y.approxRange.inverse)
    val kAA = RationalForm(tightInverse)

    val xAA = RationalForm(this.realInterval)
    val xErr = this.error

    val yInt = y.interval
    val a = min(abs(yInt.xlo), abs(yInt.xhi))
    // make this negOne constant or sth like that
    val errorMultiplier = Rational(-1l, 1l) / (a*a)
    val gErr = y.error * new RationalForm(errorMultiplier)
    
    // Now do the multiplication x * (1/y)
    val newTree = FDivision(this.tree, y.tree)
    val newApprox = this.approxRange / y.approxRange

    val newRange = getTightInterval(newTree, newApprox)
    val rndoff = roundoff(newRange)
    
    val newError = addNoise(xAA*gErr + kAA*xErr + xErr*gErr, rndoff)
    if(verbose) println("\ndivision, newRange: " + newRange)
    if(verbose) println("            roundoff: " + rndoff)
    return new XFloat(newTree, newApprox, newError, solver)
  }

  override def toString: String = this.interval.toString + " - (" +
    this.maxRoundoff + ")(abs)" 

  private def getTightInterval(tree: Expr, approx: RationalForm): RationalInterval = {
    //println("\ncomputing tight range for " + tree)
    val appInt = approx.interval
    //println("initial range: " + appInt)
    //println(appInt.xlo.toFractionString + "   -  " + appInt.xhi.toFractionString)

    /*if (tree.toString == "(((2.625 - x) + (((x * y) * (x * y)) * (x * y))) * ((2.625 - x) + (((x * y) * (x * y)) * (x * y))))" ) {
      BoundsIterator.verbose = true
    }*/

    // Fix the scaling issue
    val res = BoundsIterator.tightenRange(solver, tree, new RationalInterval(approx.intervalDouble))
    //BoundsIterator.verbose = false
    res
  }
}
