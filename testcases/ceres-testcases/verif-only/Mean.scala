

import leon.Real
import Real._


object Mean {

  /*
    Computing the mean.
    In the original benchmark, the numbers are read from a file.
  */
  //invariant(meanSpec() <= meanImpl())

  def meanSpec(x1: Real, x2: Real, x3: Real, x4: Real, x5: Real, x6: Real): Real = {
    require(x1 in [-1200, 1200])

    (x1 + x2 + x3 + x4 + x5 + x6) / 6.0  
  }


  def meanImpl(x1: Real, x2: Real, x3: Real, x4: Real, x5: Real, x6: Real): Real = {
    require(x1 in [-1200, 1200])

    val i1 = x1
    val i2 = (x + x2)/2.0
    val i3 = (2*x + x3)/3.0
    val i4 = (3*x + x4)/4.0
    val i5 = (4*x + x5)/5.0
    val i6 = (5*x + x6)/6.0
    i6
  }
}
