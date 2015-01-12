/* Copyright 2009-2015 EPFL, Lausanne */

import RealOps._

object SimplePathErrorsUnknown {

  def squareRoot3Invalid(x: Real): Real = {
    require(0 < x && x < 10 && x +/- 1e-10 )
    if (x < 1e-4) 1 + 0.5 * x
    else sqrt(1 + x)
  } ensuring( res => res +/- 1e-10) //invalid

}