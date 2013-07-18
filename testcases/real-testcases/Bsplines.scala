
import leon.Real
import Real._

/**
  Equations and initial ranges from:
  L. Zhang, Y. Zhang, and W. Zhou. Tradeoff between Approximation Accuracy and
  Complexity for Range Analysis using Affine Arithmetic.
*/
object Bsplines {

  def bspline0(u: Real): Real = {
    require(u >< (0.0, 1.0) && u +/- 1e-9)
  
    assert(u * sqrt(u) <= 0.5)
  
    (1 - u) * (1 - u) * (1 - u)/6.0
  } ensuring (res => -0.05 <= ~res && ~res <= 0.17 && res +/- 1e-15)
  
  /*def bspline1(u: Real): Real = {
    require(0 <= u && u <= 1)
    (3 * u*u*u - 6 * u*u + 4) / 6.0
  } ensuring (res => -0.05 <= res && res <= 0.98 && res +/- 1e-15)
  
  def bspline2(u: Real): Real = {
    require(0 <= u && u <= 1)
    (-3 * u*u*u  + 3*u*u + 3*u + 1) / 6.0
  } ensuring (res => -0.02 <= res && res <= 0.89 && res +/- 1e-15)

  def bspline3(u: Real): Real = {
    require(0 <= u && u <= 1)
    -u*u*u / 6.0
  } ensuring (res => -0.17 <= res && res <= 0.05 && res +/- 1e-15)
  */
}
