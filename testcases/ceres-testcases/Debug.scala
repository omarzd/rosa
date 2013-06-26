


import leon.Real
import Real._



object Debug {

  def quadraticClassicRoot1(a: Real, b: Real, c: Real): Real = {
    require(a.in(2.5, 3.5) && b.in(54.0, 57.0) && c.in(0.5, 1.5))
    val discr = b*b - a * c * 4.0

    (-b - sqrt(discr))/(a * 2.0)
  } ensuring (res => noise(res, 1e-13))

  def quadraticSmartRoot2(a: Real, b: Real, c: Real): Real = {
    require(a.in(2.5, 3.5) && b.in(54.0, 57.0) && c.in(0.5, 1.5))

    val discr = b*b - a * c * 4.0

    if(b*b - a*c > 10.0) {
      if(b > 0.0) c * 2.0 /(-b - sqrt(discr))
      else if(b < 0.0)  (-b + sqrt(discr))/(a * 2.0)
      else (-b + sqrt(discr))/(a * 2.0)
    }
    else {
      (-b + sqrt(discr))/(a * 2.0)
    }
  } ensuring (res => noise(res, 1e-13))
}
