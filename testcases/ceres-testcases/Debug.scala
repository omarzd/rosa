


import leon.Real
import Real._

import leon.Utils._

object Debug {

  def triangleStable(a: Real, b: Real, c: Real): Real = {
    require(1.0 <= a && a <= 9.0 && 4.0 <= b && b <= 4.0 && 5.0 <= c && c <= 5.0 &&
      a + b > c + 0.1 && a + c > b + 0.1 && b + c > a + 0.1 && a < c && b < c)

    if (a < b) { // a < b < c
      ((c+(b+a)) * (a-(c-b)) * (a+(c-b)) * (c+(b-a))) / 4.0
    } else {
      val s = ((a + b + c)/2.0)
      (s * (s - a) * (s - b) * (s - c))
    }
  } ensuring (res => res +/- 1e-10)

  /*def triangleStable(a: Real, b: Real, c: Real): Real = {
    require(1.0 <= a && a <= 9.0 && 1.0 <= b && b <= 9.0 && 1.0 <= c && c <= 9.0 &&
      a + b > c + 0.1 && a + c > b + 0.1 && b + c > a + 0.1)

    if(b < a) {
      if(c < b) sqrt((a+(b+c)) * (c-(a-b)) * (c+(a-b)) * (a+(b-c))) / 4.0
      else {
        if(c < a) sqrt((a+(c+b)) * (b-(a-c)) * (b+(a-c)) * (a+(c-b))) / 4.0
        else sqrt((c+(a+b)) * (b-(c-a)) * (b+(c-a)) * (c+(a-b))) / 4.0
      }
    }
    else if(c < b) {
      if (a < c) sqrt(b+(c+a)) * (a-(b-c)) * (a+(b-c)) * (b+(c-a)) / 4.0
      else sqrt(b+(a+c)) * (c-(b-a)) * (c+(b-a)) * (b+(a-c)) / 4.0
    } else {
      sqrt(c+(b+a)) * (a-(c-b)) * (a+(c-b)) * (c+(b-a)) / 4.0
    }
  } ensuring (res => res +/- 1e-10)
  */

/*  def invariant1(y1: Real, y2: Real, y3: Real, y4: Real, y5: Real, y6: Real): Boolean = {
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
  */

  
  /*def turbine1(v: Real, w: Real, r: Real): Real = {
    require(v.in(-4.5, -0.3) && w.in(0.4, 0.9) && r.in(3.8, 7.8) && v +/- 1e-7 && w +/- 1e-5 * w && r +/- 1e-5)

    3 + (r*v*w)

  } ensuring( res => res +/- (!v + 3 * !w + 0.001))
  */
}
