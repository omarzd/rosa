/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees.{Expr}

/**
  A datatype for range arithmetic that keeps track of floating-point roundoff errors.
  @param tree expression tree
  @param approxRange approximation of the real-valued range
  @param error various uncertainties, incl. roundoffs
  @param config solver, precondition, which precision to choose
 */
abstract class XReal(val tree: Expr, val approxInterval: RationalInterval, val error: XRationalForm, val config: XFloatConfig) {

  // Interval of the real-valued part only
  val realInterval: RationalInterval

  // Interval including errors
  val interval: RationalInterval
  
  val maxError: Rational

  def unary_-(): XReal
  def +(y: XReal): XReal
  def -(y: XReal): XReal
  def *(y: XReal): XReal
  def /(y: XReal): XReal

  def squareRoot: XReal 
  
}