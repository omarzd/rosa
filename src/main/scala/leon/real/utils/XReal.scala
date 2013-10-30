/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import real.Trees._
import Rational._
import VariableShop._
import RationalAffineUtils._

/**
  A datatype for range arithmetic that keeps track of floating-point roundoff errors.
  @param tree expression tree
  @param approxRange approximation of the real-valued range
  @param config solver, precondition, which precision to choose
 */
class XReal(val tree: Expr, val approxInterval: RationalInterval, val error: XRationalForm, val config: XConfig) {
  val verbose = false

  def this(tuple: (Expr, RationalInterval, XRationalForm, XConfig)) =
    this(tuple._1, tuple._2, tuple._3, tuple._4)

  // Interval of the real-valued part only
  lazy val realInterval: RationalInterval = {
    getTightInterval(tree, approxInterval, config.getCondition)
  }

  // Interval including errors
  lazy val interval: RationalInterval = realInterval + error.interval
  
  lazy val maxError: Rational  = {
    val i = error.interval
    max(abs(i.xlo), abs(i.xhi))
  }

  /*  TODO: Ignores any (new??) errors */
  def unary_-(): XReal = new XReal(this.negate)

  def +(y: XReal): XReal = new XReal(this.add(y))
  def -(y: XReal): XReal = new XReal(this.subtract(y))
  def *(y: XReal): XReal = new XReal(this.multiply(y))
  def /(y: XReal): XReal = new XReal(this.divide(y))
  def squareRoot: XReal = new XReal(this.takeSqrtRoot)
  
  /*
    Propagation
   */
  def negate: (Expr, RationalInterval, XRationalForm, XConfig) = (UMinusR(tree), -approxInterval, -error, config)

  def add(y: XReal): (Expr, RationalInterval, XRationalForm, XConfig) = {
    if (verbose) println("Adding " + this + " to " + y)
    val newConfig = config.and(y.config)
    val newTree = PlusR(this.tree, y.tree)
    val newInterval = this.approxInterval + y.approxInterval
    var newError = this.error + y.error
    val newRealRange = getTightInterval(newTree, newInterval, newConfig.getCondition)
    (newTree, newRealRange, newError, newConfig)
  }

  def subtract(y: XReal): (Expr, RationalInterval, XRationalForm, XConfig)  = {
    if (verbose) println("Subtracting " + this + " from " + y)
    val newConfig = config.and(y.config)
    val newTree = MinusR(this.tree, y.tree)
    val newInterval = this.approxInterval - y.approxInterval
    var newError = this.error - y.error
    val newRealRange = getTightInterval(newTree, newInterval, newConfig.getCondition)
    (newTree, newRealRange, newError, newConfig)
  }

  def multiply(y: XReal): (Expr, RationalInterval, XRationalForm, XConfig) = {
    if (verbose) println("Mult " + this.tree + " with " + y.tree)
    if (verbose) println("x.error: " + this.error.longString)
    if (verbose) println("y.error: " + y.error.longString)
    val newConfig = config.and(y.config)
    val newTree = TimesR(this.tree, y.tree)
    val newInterval = this.approxInterval * y.approxInterval

    val xAA = XRationalForm(this.realInterval)
    val yAA = XRationalForm(y.realInterval)
    val yErr = y.error
    val xErr = this.error

    var newError = xAA*yErr + yAA*xErr + xErr*yErr
    val newRealRange = getTightInterval(newTree, newInterval, newConfig.getCondition)
    (newTree, newRealRange, newError, newConfig)
  }

  def divide(y: XReal): (Expr, RationalInterval, XRationalForm, XConfig) = {
    //if (y.isExact) {

    // Compute approximation
    //val tightInverse = getTightInterval(Division(new RealLiteral(1), y.tree), y.approxRange.inverse)
    val tightInverse = getTightInterval(DivisionR(new RealLiteral(1), y.tree), RationalInterval(one, one)/y.approxInterval, y.config.getCondition)
    val kAA = XRationalForm(tightInverse)
    val xAA = XRationalForm(this.realInterval)
    val xErr = this.error

    val yInt = y.interval
    val a = min(abs(yInt.xlo), abs(yInt.xhi))
    val errorMultiplier = -one / (a*a)
    val gErr = y.error * new XRationalForm(errorMultiplier)

    // Now do the multiplication x * (1/y)
    val newConfig = config.and(y.config)
    val newTree = DivisionR(this.tree, y.tree)
    val newInterval = this.approxInterval / y.approxInterval

    var newError = xAA*gErr + kAA*xErr + xErr*gErr
    val newRealRange = getTightInterval(newTree, newInterval, newConfig.getCondition)
    (newTree, newRealRange, newError, newConfig)
  }

  def takeSqrtRoot: (Expr, RationalInterval, XRationalForm, XConfig) = {
    // if this.isExact

    val int = this.interval
    val a = min(abs(int.xlo), abs(int.xhi))
    val errorMultiplier = Rational(1l, 2l) / sqrtDown(a)

    //val newTree = Sqrt(this.tree)
    val (sqrtVar, n) = getNewSqrtVariablePair
    val newTree = sqrtVar
    val newCondition = And(Equals(TimesR(sqrtVar, sqrtVar), this.tree), LessEquals(RealLiteral(zero), sqrtVar))
    val newConfig = config.addCondition(newCondition)

    val newInterval = RationalInterval(sqrtDown(this.approxInterval.xlo), sqrtUp(this.approxInterval.xhi))

    var newError = this.error * new XRationalForm(errorMultiplier)
    val newRealRange = getTightInterval(newTree, newInterval, newConfig.getCondition)
    (newTree, newRealRange, newError, newConfig)
  }


  private def getTightInterval(tree: Expr, approx: RationalInterval, condition: Expr): RationalInterval = {
    //println("\n tightening: " + tree)
    //println("with pre: " + condition)
    val massagedTree = TreeOps.massageArithmetic(tree)
    //println("massaged: " + massagedTree)
    //println("initial approx: " + approx)

    /*val eps2 = Variable(FreshIdentifier("#eps2")).setType(RealType)
    val boundsConverter = new BoundsConverter(eps2, eps)
    val toCheck2 = boundsConverter.transform(toCheck)
    println("\n new to Check:")
    println(toCheck2)
    //toCheck = toCheck2*/

    val res = config.solver.tightenRange(massagedTree, condition, approx, config.solverMaxIter, config.solverPrecision)
    //println(tree + "  " + config.solverMaxIter)
    //val res = approx
    //println("after tightening: " + res)

    return res
  }
  
}