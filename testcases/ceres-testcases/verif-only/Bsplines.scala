
import leon.Real
import Real._

/** 
  Equations and initial ranges from:
  L. Zhang, Y. Zhang, and W. Zhou. Tradeoff between Approximation Accuracy and
  Complexity for Range Analysis using Affine Arithmetic.
*/
object BsplinesRealsOnly {

  // TODO: it should be 1/6 throughout, but we cannot handle that atm.

  def bspline0(u: Real): Real = {
    require(0 <= u && u <= 1 && roundoff(u))
    (1 - u) * (1 - u) * (1 - u) * 0.1666666
  } ensuring (res => -0.05 <= res && res <= 0.17 && noise(res) <= 1e-14)
  

  def bspline1(u: Real): Real = {
    require(0 <= u && u <= 1 && roundoff(u))
    (3 * u*u*u - 6 * u*u + 4) * 0.1666666
  } ensuring (res => -0.05 <= res && res <= 0.98 && noise(res) <= 1e-14)
  

  def bspline2(u: Real): Real = {
    require(0 <= u && u <= 1 && roundoff(u))
    (-3 * u*u*u  + 3*u*u + 3*u + 1) * 0.1666666
  } ensuring (res => -0.02 <= res && res <= 0.89 && noise(res) <= 1e-14)
  
  def bspline3(u: Real): Real = {
    require(0 <= u && u <= 1 && roundoff(u))
    -u*u*u * 0.1666666
  } ensuring (res => -0.17 <= res && res <= 0.05 && noise(res) <= 1e-14)


}
