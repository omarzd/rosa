


import leon.Real
import Real._



object Debug {

  /*def bspline3(u: Real): Real = {
    require(0 <= u && u <= 1)
    -u*u*u / 6.0
  } ensuring (res => -0.17 <= res && res <= 0.05 && noise(res, 1e-15))
  */

  /*def quadraticClassicRoot1(a: Real, b: Real, c: Real): Real = {
    require(a.in(2.5, 3.5) && b.in(54.0, 57.0) && c.in(0.5, 1.5))
    val discr = b*b - a * c * 4.0

    //(-b - sqrt(discr))/(a * 2.0)
    discr
  } ensuring (res => noise(res, 1e-11))
  */

  def quadraticClassicRoot1(a: Real): Real = {
    require(a.in(2.5, 3.5))
    
    //a/(a * c)
    1.0/(a * 2.0)
    //2.0 * a
  } ensuring (res => noise(res, 1e-11))
  
}
