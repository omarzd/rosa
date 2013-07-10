


import leon.Real
import Real._

import leon.Utils._

object Debug {

  
  def turbine1(v: Real, w: Real, r: Real): Real = {
    require(v.in(-4.5, -0.3) && w.in(0.4, 0.9) && r.in(3.8, 7.8) && v +/- 1e-7 && w +/- 1e-12 && r +/- 1e-8)

    3 + 2/(r*r) - 0.125*f(v, w)
  } ensuring (res => res +/- 1e-6)
  
  def f(v: Real, w: Real): Real = {
    require(v.in(-4.5, -0.3) && w.in(0.4, 0.9) && v +/- 1e-7 && w +/- 1e-5)

    v + 3 * w

  } ensuring( res => -4.5 <= res && res <= 0.0 &&  res +/- (!v + 3 * !w))
  
}
