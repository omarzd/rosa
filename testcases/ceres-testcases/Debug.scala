


import leon.Real
import Real._



object Debug {

  /*def rigidBody(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 15 && x1 >= -15 && x2 <= 15 && x2 >= -15 &&
            x3 <= 15 && x3 >= -15 && roundoff(x1) && roundoff(x2) && roundoff(x3))
    -x1*x2 - 2*x2*x3 - x1 - x3
  } ensuring (res => -800 <= res && res <= 750.0 && noise(res, 1e-10))
  */

  def mult(y2: Real, y3: Real): Real = {
    require(-15 <= y2 && y2 <= 15 && -15 <= y3 && y3 <= 15 && roundoff(y2, y3))
    y2 * y3
  } ensuring (res => -225 <= res && res <= 225 && noise(res, 1e-13))


  def rigidBody1(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 15 && x1 >= -15 && x2 <= 15 && x2 >= -15 &&
            x3 <= 15 && x3 >= -15 && roundoff(x1) && roundoff(x2) && roundoff(x3))
    -mult(x1,x2) - 2*mult(x2, x3) - x1 - x3
  } ensuring (res => -800 <= res && res <= 750.0 && noise(res, 1e-10))


  /*
  def rigidBody11(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 15 && x1 >= -15 && x2 <= 15 && x2 >= -15 &&
            x3 <= 15 && x3 >= -15 && roundoff(x1) && roundoff(x2) && roundoff(x3))
    val t1 = -mult(x1,x2)
    val t2 = - x1 - x3
    t1 - 2*mult(x2, x3) + t2
  } ensuring (res => -800 <= res && res <= 750.0 && noise(res, 1e-10))


  def rigidBody12(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 15 && x1 >= -15 && x2 <= 15 && x2 >= -15 &&
            x3 <= 15 && x3 >= -15 && roundoff(x1) && roundoff(x2) && roundoff(x3))
    if (x1 < 3.4) {
      val t1 = -mult(x1,x2)
      val t2 = - x1 - x3
      t1 - 2*mult(x2, x3) + t2
    } else {
      -mult(x1,x2) - 2*mult(x2, x3) - x1 - x3
    }

  } ensuring (res => -800 <= res && res <= 750.0 && noise(res, 1e-10))
  */

  /*def f(x: Real): Real = {
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
  */

}
