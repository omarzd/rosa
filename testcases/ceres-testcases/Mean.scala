

import leon.Real
import Real._

import leon.Utils._

/*
This benchmark is inspired from the
FEVS - Functional Equivalence Verification Suite
vsl.cis.udel.edu/fevs
*/
object Mean {

  /*
    Computing the mean.
    In the original benchmark, the numbers are read from a file.
  */

  def invariant(x1: Real, x2: Real, x3: Real, x4: Real, x5: Real, x6: Real): Boolean = {
    require(x1.in(-1200, 1200) && x2.in(-1200, 1200) && x3.in(-1200, 1200) &&
     x4.in(-1200, 1200) && x5.in(-1200, 1200) && x6.in(-1200, 1200) && roundoff(x1, x2, x3, x4, x5) && roundoff(x6))

    meanSpec(x1, x2, x3, x4, x5, x6) <= meanImpl(x1, x2, x3, x4, x5, x6)
  } holds


  def meanSpec(x1: Real, x2: Real, x3: Real, x4: Real, x5: Real, x6: Real): Real = {
    require(x1.in(-1200, 1200) && x2.in(-1200, 1200) && x3.in(-1200, 1200) &&
     x4.in(-1200, 1200) && x5.in(-1200, 1200) && x6.in(-1200, 1200) && roundoff(x1, x2, x3, x4, x5) && roundoff(x6))

    (x1 + x2 + x3 + x4 + x5 + x6) / 6.0
  }


  def meanImpl(x1: Real, x2: Real, x3: Real, x4: Real, x5: Real, x6: Real): Real = {
    require(x1.in(-1200, 1200) && x2.in(-1200, 1200) && x3.in(-1200, 1200) &&
     x4.in(-1200, 1200) && x5.in(-1200, 1200) && x6.in(-1200, 1200) && roundoff(x1, x2, x3, x4, x5) && roundoff(x6))


    val i1 = x1
    val i2 = (i1 + x2)/2.0
    val i3 = (2*i2 + x3)/3.0
    val i4 = (3*i3 + x4)/4.0
    val i5 = (4*i4 + x5)/5.0
    val i6 = (5*i5 + x6)/6.0
    i6
  }
}
