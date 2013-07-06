


import leon.Real
import Real._

import leon.Utils._

object Debug {

  def invariant1(y1: Real, y2: Real, y3: Real, y4: Real, y5: Real, y6: Real): Boolean = {
    require(y1.in(-1200, 1200) && y2.in(-1200, 1200) && y3.in(-1200, 1200) &&
     y4.in(-1200, 1200) && y5.in(-1200, 1200) && y6.in(-1200, 1200))

    val m1 = meanSpec(y1, y2, y3, y4, y5, y6)
    val m2 = meanImpl(y1, y2, y3, y4, y5, y6)
    ~m1 <= ~m2 + 0.01
  } holds
  

  def meanSpec(x1: Real, x2: Real, x3: Real, x4: Real, x5: Real, x6: Real): Real = {
    require(x1.in(-1200, 1200) && x2.in(-1200, 1200) && x3.in(-1200, 1200) &&
     x4.in(-1200, 1200) && x5.in(-1200, 1200) && x6.in(-1200, 1200))

    (x1 + x2 + x3 + x4 + x5 + x6) / 6.0
  } ensuring(res => res <= 1200.0 && -1200.0 <= res && res +/- (!x1 + !x2))


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
  } ensuring(res => res <= 1200.0 && -1200.0 <= res && res +/- 1e-10)


  
  /*def turbine1(v: Real, w: Real, r: Real): Real = {
    require(v.in(-4.5, -0.3) && w.in(0.4, 0.9) && r.in(3.8, 7.8) && v +/- 1e-7 && w +/- 1e-5 * w && r +/- 1e-5)

    3 + (r*v*w)

  } ensuring( res => res +/- (!v + 3 * !w + 0.001))
  */
}
