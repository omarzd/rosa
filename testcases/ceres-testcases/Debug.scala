


import leon.Real
import Real._

import leon.Utils._

object Debug {

  def test(x: Real): Real = {
    require(x.in(-5.0, 5.0) && noise(x, 1e-10))
    if(x < 0) {
        x*x
      } else {
        2*x
      }
  } ensuring(res => noise(res, 1e-8))

  def test2(x: Real): Real = {
    require(x.in(-5.0, 5.0) && noise(x, 1e-10))
    if(x < 0) {
      x*x
    } else {
      2*x + 0.1
    }
  } ensuring(res => noise(res, 1e-8))
}
