

import leon.Real
import Real._

object Misc {

  def booths(x: Real, y: Real): Real = {
    require(-9 <= x && x <= -5 && 1 <= y && y <= 3)
    (x + 2*y -7)*(x + 2*y -7) + (2*x + y -5)*(2*x + y -5)
  } ensuring (res => 180.0 <= res && res <= 678.0 && noise(res, 1e-12))

  def camel(x: Real, y: Real): Real = {
    require(-5 <= x && x <= 5 && -5 <= y && y <= 5)
    2*x*x - 1.05*x*x*x*x + (x*x*x*x*x*x)/6 + x*y + y*y
  } ensuring (res => 0.0 <= res && res <= 2048.0 && noise(res, 1e-11))


  def goldstein(x: Real, y: Real): Real = {
    require(-1.5 <= x && x <= 0.5 && 0.5 <= y && y <= 1.5)
    (1 + (x + y + 1)*(x + y + 1) *(19 - 14*x + 3*x*x - 14*y + 6*x*y + 3*y*y)) *
    (30 + (2*x - 3*y)*(2*x - 3*y) * (18 - 32*x + 12*x*x +48*y - 36*x*y + 27*y*y))
  } ensuring (res => res >= -56020.0)


  def matyas(x: Real, y: Real): Real  = {
    require(-9 <= x && x <= -5 && 1 <= y && y <= 3)
    0.26*(x*x + y*y) - 0.48*x*y
  } ensuring (res => 9.1 <= res && res <= 36.4 && noise(res, 1e-13))

  def motzkin(x: Real, y: Real, z: Real): Real = {
    require(-5.6 <= x && x <= 1.3 && 45.3 <= y && y <= 63.0 &&
            3.2 <= z && z <= 15.7)
    z*z*z + x*x*(y*y) * (z*z + y*y - 3*z*z)
  } ensuring (res => 36.0 <= res && res <= 486842460.0 && noise(res, 1e-6))


  def poly1(x: Real): Real = {
    require(-1.24 <= x && x <= 3.5)
    1 - (x*x)/2.0 + (x*x*x*x)/24.0 - (x*x*x*x*x*x)/720.0
  } ensuring (res => -1.43 <= res && res <= 1.0 && noise(res, 1e-12))


  def poly2(x: Real): Real = {
    require(-1.23 <= x && x <= 2.34)
    1 + (x*x)/2.0 + (x*x*x*x)/24.0 + (x*x*x*x*x*x)/720.0
  } ensuring (res => 1.0 <= res && res <= 5.5 && noise(res, 1e-12))

  def poly3(x: Real): Real = {
    require(-1.5 <= x && x <= 0.8)
    1 + x + x*x + (2*x*x*x)/3.0 + (x*x*x*x)/2.0
  } ensuring (res => 0.7 <= res && res <= 3.0 && noise(res, 1e-12))


}