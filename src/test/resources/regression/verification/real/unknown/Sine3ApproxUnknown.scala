/* Copyright 2009-2015 EPFL, Lausanne */

import RealOps._

//http://www.coranac.com/2009/07/sines/
object Sine3ApproxUnknown {

  def sineOrder3(x: Real): Real = {
    require(-2.0 < x && x < 2.0)
    0.954929658551372 * x -  0.12900613773279798*(x*x*x)
  } ensuring(res => -1.0 < ~res && ~res < 1.0 && res +/- 1e-14)

}