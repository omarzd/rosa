


import leon.Real
import Real._



object Debug {

  def f(x: Real): Real = {
    require(0 <= x && x <= 2.3 && noise(x, 1e-7))
    val t = if (x <= 1.2) {
      if (x <= 2.0)
        x * x
      else
        2 * x
    } else {
      val t2 = x * x
      x * t2
    }
    t
  } ensuring (res => res >= 0 && noise(res, 1e-5))




  def rigidBody1(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 15 && x1 >= -15 && x2 <= 15 && x2 >= -15 &&
            x3 <= 15 && x3 >= -15 && roundoff(x1) && roundoff(x2) && roundoff(x3))
    -x1*x2 - 2*x2*x3 - x1 - x3
  } ensuring (res => -800 <= res && res <= 750.0 && noise(res, 1e-10))



  def f5(x: Real): Real = {
    require(0 <= x && x <= 2.3 && noise(x, 1e-7))
    val y = x * x - 3.4
    val temp = if (x + y <= 0) {
      val t1 = x * y
      2*x + t1
    } else {
      5*x
    }
    temp
  } ensuring (res => res >= 0 && noise(res, 1e-5))


  def f6(x: Real): Real = {
    require(0 <= x && x <= 2.3 && noise(x, 1e-7))
    val y = x * x - 3.4
    if (x + y <= 0) {
      val t1 = x * y
      2*x + t1
    } else {
      5*x
    }
  } ensuring (res => res >= 0 && noise(res, 1e-5))

  def f7(x: Real): Real = {
    require(0 <= x && x <= 2.3 && noise(x, 1e-7))
    if (x < 1.2)
      x * x
    else
      x * x * x

  } ensuring (res => res >= 0 && noise(res, 1e-5))


}
