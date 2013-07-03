


import leon.Real
import Real._

import leon.Utils._

object Debug {

  def verhulst(r: Real, K: Real, x: Real): Real = {
    require(r.in(4.0,4.0) && K >= 1.11 && K <= 1.11 && x.in(0.1, 0.3) &&
      noise(r, 0.001) && noise(K, 1e-5) && noise(x, 1e-6))

    (r*x) / (1 + (x/K))

  } ensuring (res => res <= 0.0)


}
