


import leon.Real
import Real._



object Debug {

  /*def bspline3_0(u: Real): Real = {
    require(0 <= u && u <= 1)
    -u*u*u / 6.0
  } ensuring (res => -0.17 <= res && res <= 0.05 && noise(res, 1e-5))

  def bspline3_1(u: Real): Real = {
    require(0 <= u && u <= 1)
    -u*u*u / 6.0
  } ensuring (res => -0.17 <= res && res <= 0.05 && noise(res, 1e-15))
  */

  def bspline3_2(u: Real): Real = {
    require(0 <= u && u <= 1)
    -u*u*u / 6.0
  } ensuring (res => -0.17 <= res && res <= 0.05 && noise(res, 1e-19))


}
