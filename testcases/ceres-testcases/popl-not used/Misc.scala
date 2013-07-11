

import leon.Real
import Real._

object Misc {

  def booths(x: Real, y: Real): Real = {
    require(x.in(-9,-5) && y.in(1,3))
    (x + 2*y -7)*(x + 2*y -7) + (2*x + y -5)*(2*x + y -5)
  } 

  def camel(x: Real, y: Real): Real = {
    require(x.in(-5, 5) && y.in(-5, 5))
    2*x*x - 1.05*x*x*x*x + (x*x*x*x*x*x)/6 + x*y + y*y
  }

  def goldstein(x: Real, y: Real): Real = {
    require(x.in(-1.5, 0.5) && y.in(0.5,1.5))
    (1 + (x + y + 1)*(x + y + 1) *(19 - 14*x + 3*x*x - 14*y + 6*x*y + 3*y*y)) *
    (30 + (2*x - 3*y)*(2*x - 3*y) * (18 - 32*x + 12*x*x +48*y - 36*x*y + 27*y*y))
  }

  def matyas(x: Real, y: Real): Real  = {
    require(x.in(-9,-5) && y.in(1,3))
    0.26*(x*x + y*y) - 0.48*x*y
  }

  def motzkin(x: Real, y: Real, z: Real): Real = {
    require(x.in(-5.6,1.3) && y.in(45.3,63.0) && z.in(3.2,15.7))
    z*z*z + x*x*(y*y) * (z*z + y*y - 3*z*z)
  }

  def poly1(x: Real): Real = {
    require(x.in(-1.24,3.5))
    1 - (x*x)/2.0 + (x*x*x*x)/24.0 - (x*x*x*x*x*x)/720.0
  }

  def poly2(x: Real): Real = {
    require(x.in(-1.23, 2.34))
    1 + (x*x)/2.0 + (x*x*x*x)/24.0 + (x*x*x*x*x*x)/720.0
  }

  def poly3(x: Real): Real = {
    require(x.in(-1.5, 0.8))
    1 + x + x*x + (2*x*x*x)/3.0 + (x*x*x*x)/2.0
  }

}