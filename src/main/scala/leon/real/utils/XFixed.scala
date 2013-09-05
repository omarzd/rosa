/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees.{Expr}

class XFixed(val tr: Expr, val appInt: RationalInterval, val err: XRationalForm, val cnfg: XFloatConfig) extends XReal(tr, appInt, err, cnfg) {

  lazy val realInterval: RationalInterval = null

  lazy val interval: RationalInterval = null
  
  lazy val maxError: Rational = null

  def unary_-(): XReal = null
  def +(y: XReal): XReal = null
  def -(y: XReal): XReal = null
  def *(y: XReal): XReal = null
  def /(y: XReal): XReal = null

  def squareRoot: XReal = null

}