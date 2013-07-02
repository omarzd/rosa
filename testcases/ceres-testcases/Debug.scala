


import leon.Real
import Real._



object Debug {

  /*
  def dopplerOriginalOriginal(u: Real, v: Real, T: Real): Real = {
    require(-100 <= u && u <= 100 && 20 <= v && v <= 20000 &&
     -30 <= T && T <= 50 && noise(u, 1e-7) && noise(v, 1e-9) && noise(T, 1e-6))

    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))

  } ensuring (res => -138.0 <= res && res <= -0.03 && noise(res, 1e-4))
  */


  /*def dopplerOriginal(u: Real, v: Real, T: Real): Real = {
    require(-100 < u && u < 100 && 20 < v && v < 20000 &&
     -30 < T && T < 50 && noise(u, 1e-7) && noise(v, 1e-9) && noise(T, 1e-6))

    val x = 331.4 + 0.6 * T
    val x2 = (x + u) * (x + u)
    (- x * v) / x2

  } ensuring (res => -200.0 < res && res < 0)// && noise(res, 1e-4))
  */

  def doppler(u: Real, v: Real, T: Real): Real = {
    require(-100 <= u && u <= 100 && 20 <= v && v <= 20000 &&
     -30 <= T && T <= 50 && noise(u, 1e-7) && noise(v, 1e-9) && noise(T, 1e-6))

    val x = mult(T)
    val x2 = x + u
    (- x * v) / (x2 * x2)

  } ensuring (res => -138.0 <= res && res <= -0.03 && noise(res, 1e-4))


  def mult(T: Real): Real = {
    require(-30 <= T && T <= 50 && noise(T, 1e-6))
    331.4 + 0.6 * T
  }



  /*def bspline3(u: Real): Real = {
    require(0 <= u && u <= 1)
    -u*u*u / 6.0
  } ensuring (res => -0.17 <= res && res <= 0.05 && noise(res, 1e-15))
  */


  /*def rigidBody1Original(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 15 && x1 >= -15 && x2 <= 15 && x2 >= -15 &&
            x3 <= 15 && x3 >= -15)
    -x1*x2 - 2*x2*x3 - x1 - x3
  } ensuring (res => -800 <= res && res <= 750.0 && noise(res, 1e-10))


  def rigidBody1(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 15 && x1 >= -15 && x2 <= 15 && x2 >= -15 &&
            x3 <= 15 && x3 >= -15)
    -mult(x1, x2) - 2*mult(x2, x3) - x1 - x3
  } ensuring (res => -800 <= res && res <= 750.0 && noise(res, 4e-13))

  def mult(x1: Real, x2: Real): Real = {
    require(x1 <= 15 && x1 >= -15 && x2 <= 15 && x2 >= -15 )
    x1*x2
  }
  */

}
