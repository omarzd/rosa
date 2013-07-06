


import leon.Real
import Real._

import leon.Utils._

object Debug {

  def turbine1(v: Real, w: Real, r: Real): Real = {
    require(v.in(-4.5, -0.3) && w.in(0.4, 0.9) && r.in(3.8, 7.8) && v +/- 1e-7 && w +/- 1e-5 * w && r +/- 1e-5)

    3 + (r*v*w)

  } ensuring( res => res +/- (!v + 3 * !w + 0.001))

}
