import leon.Real
import Real._

import leon.Utils._

object Counterexamples {

  def test(y1: Real, y2: Real, y3: Real, y4: Real, y5: Real, y6: Real): Boolean = {
    require(y1.in(-1200, 1200) && y2.in(-1200, 1200) && y3.in(-1200, 1200) &&
     y4.in(-1200, 1200) && y5.in(-1200, 1200) && y6.in(-1200, 1200))

    val x = if (y1 < 0) {
      meanSpec(y1, y2, y3, y4, y5, y6)  
    } else {
      meanImpl(y1, y2, y3, y4, y5, y6)
    }
    x <= 0  // this does not hold, but can we get useful counterexample?
  } holds // ensuring (res => noise(res, 1e-7))

  def meanSpec(x1: Real, x2: Real, x3: Real, x4: Real, x5: Real, x6: Real): Real = {
    require(x1.in(-1200, 1200) && x2.in(-1200, 1200) && x3.in(-1200, 1200) &&
     x4.in(-1200, 1200) && x5.in(-1200, 1200) && x6.in(-1200, 1200))

    (x1 + x2 + x3 + x4 + x5 + x6) / 6.0
  }

  def meanImpl(x1: Real, x2: Real, x3: Real, x4: Real, x5: Real, x6: Real): Real = {
    require(x1.in(-1200, 1200) && x2.in(-1200, 1200) && x3.in(-1200, 1200) &&
     x4.in(-1200, 1200) && x5.in(-1200, 1200) && x6.in(-1200, 1200))

    val i1 = x1
    val i2 = (i1 + x2)/2.0
    val i3 = (2*i2 + x3)/3.0
    val i4 = (3*i3 + x4)/4.0
    val i5 = (4*i4 + x5)/5.0
    val i6 = (5*i5 + x6)/6.0
    i6
  }

}