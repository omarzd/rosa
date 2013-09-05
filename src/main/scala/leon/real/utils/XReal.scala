/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees.{Expr}

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