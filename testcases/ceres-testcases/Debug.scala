


import leon.Real
import Real._



object Debug {

  def newton1(in: Real): Real = {
    require(in > -1.2 && in < 1.2)

    val x1 = in - (in - (in*in*in)/6.0 + (in*in*in*in*in)/120.0 + (in*in*in*in*in*in*in)/5040.0)/(1 - (in*in)/2.0 + (in*in*in*in)/24.0 + (in*in*in*in*in*in)/720.0)
    val x2 = x1 - (x1 - (x1*x1*x1)/6.0 + (x1*x1*x1*x1*x1)/120.0 + (x1*x1*x1*x1*x1*x1*x1)/5040.0)/(1 - (x1*x1)/2.0 + (x1*x1*x1*x1)/24.0 + (x1*x1*x1*x1*x1*x1)/720.0)
    //val x3 = x2 - (x2 - (x2*x2*x2)/6.0 + (x2*x2*x2*x2*x2)/120.0 + (x2*x2*x2*x2*x2*x2*x2)/5040.0)/(1 - (x2*x2)/2.0 + (x2*x2*x2*x2)/24.0 + (x2*x2*x2*x2*x2*x2)/720.0)
    x2
  } ensuring(res => res < 0.1)

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
