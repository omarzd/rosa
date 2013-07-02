


import leon.Real
import Real._



object Debug {

  def smartRoot2(a: Real, b: Real, c: Real): Real = {
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

  /*def bspline3(u: Real): Real = {
    require(0 <= u && u <= 1)
    -u*u*u / 6.0
  } ensuring (res => -0.17 <= res && res <= 0.05 && noise(res, 1e-15))
  */

  /*def newton1(in: Real): Real = {
    require(in > -1.2 && in < 1.2)

    val x1 = in - (in - (in*in*in)/6.0 + (in*in*in*in*in)/120.0 + (in*in*in*in*in*in*in)/5040.0)/(1 - (in*in)/2.0 + (in*in*in*in)/24.0 + (in*in*in*in*in*in)/720.0)
    val x2 = x1 - (x1 - (x1*x1*x1)/6.0 + (x1*x1*x1*x1*x1)/120.0 + (x1*x1*x1*x1*x1*x1*x1)/5040.0)/(1 - (x1*x1)/2.0 + (x1*x1*x1*x1)/24.0 + (x1*x1*x1*x1*x1*x1)/720.0)
    //val x3 = x2 - (x2 - (x2*x2*x2)/6.0 + (x2*x2*x2*x2*x2)/120.0 + (x2*x2*x2*x2*x2*x2*x2)/5040.0)/(1 - (x2*x2)/2.0 + (x2*x2*x2*x2)/24.0 + (x2*x2*x2*x2*x2*x2)/720.0)
    x2
  } ensuring(res => res < 0.1)
  */
  /*def f(x: Real): Real = {
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  }

  def fp(x: Real): Real = {
    1 - (x*x)/2.0 + (x*x*x*x)/24.0 + (x*x*x*x*x*x)/720.0
  }

  // valid
  def newton1(in: Real): Real = {
    require(in > -0.2 && in < 0.2)
    val x1 = in - f(in)/fp(in)
    val x2 = x1 - f(x1)/fp(x1)
    //val x3 = x2 - f(x2)/fp(x2)
    x2
  } ensuring(res => ~res < 0.1)
  */


}
