


import leon.Real
import Real._



object Debug {

  def quadraticClassicRoot1(a: Real, b: Real, c: Real): Real = {
    require(a.in(2.5, 3.5) && b.in(54.0, 57.0) && c.in(0.5, 1.5))
    val discr = b*b - a * c * 4.0

    (-b - sqrt(discr))/(a * 2.0)
  } ensuring (res => noise(res, 1e-13))
}
