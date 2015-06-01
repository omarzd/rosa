/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import real.Trees._
import real.TreeOps.{getClauses}
import Rational._
import VariableShop._
import RationalAffineUtils._


object XReal {

  var solverTime = 0l

}

class XReal(val tree: Expr, val approxInterval: RationalInterval, val error: RationalForm, val config: XConfig, 
  val z3Timeout: Int) {
  val verbose = false

  def this(tuple: (Expr, RationalInterval, RationalForm, XConfig, Int)) =
    this(tuple._1, tuple._2, tuple._3, tuple._4, tuple._5)

  // Interval of the real-valued part only
  lazy val realInterval: RationalInterval = {
    getTightInterval(tree, approxInterval, config.getCondition, z3Timeout)._1
  }

  // Interval including errors
  lazy val interval: RationalInterval = realInterval + error.interval

  lazy val maxError: Rational  = {
    val i = error.interval
    max(abs(i.xlo), abs(i.xhi))
  }

  def unary_-(): XReal = new XReal(this.negate)

  def +(y: XReal): XReal = new XReal(this.add(y))
  def -(y: XReal): XReal = new XReal(this.subtract(y))
  def *(y: XReal): XReal = new XReal(this.multiply(y))
  def /(y: XReal): XReal = new XReal(this.divide(y))
  def squareRoot: XReal = new XReal(this.takeSqrtRoot)

  // Removes any constraints that do not concern the variables in the tree expression
  def cleanConfig: XReal = {
    new XReal(tree, approxInterval, error, getCleanConfig, 0)
  }

  def getCleanConfig: XConfig = {
    val clausesNeeded = TreeOps.removeRedundantConstraints(
      And(config.precondition, And(config.additionalConstraints.toSeq)), tree)
    
    val preClauses = getClauses(config.precondition)
    val preNeeded = clausesNeeded.filter(cl => preClauses.contains(cl))
    
    val additionalNeeded = clausesNeeded -- preNeeded
    
    XConfig(config.solver, And(preNeeded.toSeq), config.solverMaxIter, config.solverPrecision,
     additionalNeeded)
  }

  /*
    Propagation
   */
  def negate: (Expr, RationalInterval, RationalForm, XConfig, Int) =
    (UMinusR(tree), -approxInterval, -error, config, this.z3Timeout)

  def add(y: XReal): (Expr, RationalInterval, RationalForm, XConfig, Int) = {
    if (verbose) println("Adding " + this + " to " + y)
    val newConfig = config.and(y.config)
    val newTree = PlusR(this.tree, y.tree)
    val newInterval = this.approxInterval + y.approxInterval
    var newError = this.error + y.error
    val (newRealRange, tmOut) = getTightInterval(newTree, newInterval, newConfig.getCondition,
      (this.z3Timeout + y.z3Timeout))
    (newTree, newRealRange, newError, newConfig, tmOut + this.z3Timeout + y.z3Timeout)
  }

  def subtract(y: XReal): (Expr, RationalInterval, RationalForm, XConfig, Int)  = {
    if (verbose) println("Subtracting " + this + " from " + y)
    val newConfig = config.and(y.config)
    val newTree = MinusR(this.tree, y.tree)
    val newInterval = this.approxInterval - y.approxInterval
    var newError = this.error - y.error
    val (newRealRange, tmOut) = getTightInterval(newTree, newInterval, newConfig.getCondition,
      (this.z3Timeout + y.z3Timeout))
    (newTree, newRealRange, newError, newConfig, tmOut + this.z3Timeout + y.z3Timeout)
  }

  def multiply(y: XReal): (Expr, RationalInterval, RationalForm, XConfig, Int) = {
    if (verbose) println("Mult " + this.tree + " with " + y.tree)
    if (verbose) println("x.error: " + this.error.longString)
    if (verbose) println("y.error: " + y.error.longString)
    val newConfig = config.and(y.config)
    val newTree = TimesR(this.tree, y.tree)
    val newInterval = this.approxInterval * y.approxInterval

    val xAA = RationalForm(this.realInterval)
    val yAA = RationalForm(y.realInterval)
    val yErr = y.error
    val xErr = this.error
    var newError = xAA*yErr + yAA*xErr + xErr*yErr

    val (newRealRange, tmOut) = getTightInterval(newTree, newInterval, newConfig.getCondition,
      (this.z3Timeout + y.z3Timeout))
    (newTree, newRealRange, newError, newConfig, tmOut + this.z3Timeout + y.z3Timeout)
  }

  def divide(y: XReal): (Expr, RationalInterval, RationalForm, XConfig, Int) = {
    //if (y.isExact) {

    // Compute approximation
    //val tightInverse = getTightInterval(Division(new RealLiteral(1), y.tree), y.approxRange.inverse)
    val tightInverse = getTightInterval(DivisionR(new RealLiteral(1), y.tree),
      RationalInterval(one, one)/y.approxInterval, y.config.getCondition, y.z3Timeout)._1
    val kAA = RationalForm(tightInverse)
    val xAA = RationalForm(this.realInterval)
    val xErr = this.error

    val yInt = y.interval
    val a = min(abs(yInt.xlo), abs(yInt.xhi))
    val errorMultiplier = -one / (a*a)
    val gErr = y.error * new RationalForm(errorMultiplier)

    // Now do the multiplication x * (1/y)
    val newConfig = config.and(y.config)
    val newTree = DivisionR(this.tree, y.tree)
    val newInterval = this.approxInterval / y.approxInterval

    var newError = xAA*gErr + kAA*xErr + xErr*gErr
    val (newRealRange, tmOut) = getTightInterval(newTree, newInterval, newConfig.getCondition,
      (this.z3Timeout + y.z3Timeout))
    (newTree, newRealRange, newError, newConfig, tmOut + this.z3Timeout + y.z3Timeout)
  }

  def takeSqrtRoot: (Expr, RationalInterval, RationalForm, XConfig, Int) = {
    // if this.isExact

    val int = this.interval
    val a = min(abs(int.xlo), abs(int.xhi))
    val errorMultiplier = Rational(1L, 2L) / sqrtDown(a)

    //val newTree = Sqrt(this.tree)
    val (sqrtVar, n) = getNewSqrtVariablePair
    val newTree = sqrtVar
    val newCondition = And(Equals(TimesR(sqrtVar, sqrtVar), this.tree), LessEquals(RealLiteral(zero), sqrtVar))
    val newConfig = config.addCondition(newCondition)

    val newInterval = RationalInterval(sqrtDown(this.approxInterval.xlo), sqrtUp(this.approxInterval.xhi))

    var newError = this.error * new RationalForm(errorMultiplier)
    val (newRealRange, tmOut) = getTightInterval(newTree, newInterval, newConfig.getCondition, this.z3Timeout)
    (newTree, newRealRange, newError, newConfig, tmOut + this.z3Timeout)
  }


  private def getTightInterval(tree: Expr, approx: RationalInterval, condition: Expr,
    numTimeouts: Int): (RationalInterval, Int) = {
    
    // If Z3 has timed out before, do not try again
    if (numTimeouts > 0) {
      (approx, 0)
    } else {

      val massagedTree = TreeOps.massageArithmetic(tree)
    
      try {
        val start = System.currentTimeMillis
        val (res, timeout) = config.solver.tightenRange(massagedTree, condition, approx, config.solverMaxIter, config.solverPrecision)
        XReal.solverTime += (System.currentTimeMillis - start)

        //println("after tightening: " + res)
        (res, if(timeout) 1 else 0)
      } catch {
        case e: java.lang.AssertionError =>
          println("Exception when tightening: " + tree)
          println("with precondition: " + condition)
          println(e.getMessage)
          throw UnsoundBoundsException("unsound range for " + tree)
          null
      }
    }
  }

}
