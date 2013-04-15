


/** 
  Equations and initial ranges from:
  L. Zhang, Y. Zhang, and W. Zhou. Tradeoff between Approximation Accuracy and
  Complexity for Range Analysis using Affine Arithmetic.
*/
object Bsplines {

  def bspline0(u: Double): Double = {
    require(0 <= u && u <= 1)
    (1 - u) * (1 - u) * (1 - u) * (1.0/6.0)
  } ensuring (res => -0.05 <= res && res <= 0.17)

  def bspline1(u: Double): Double = {
    require(0 <= u && u <= 1)
    (3 * u*u*u - 6 * u*u + 4) * (1/6.0)
  } ensuring (res => -0.05 <= res && res <= 0.98)

  def bspline2(u: Double): Double = {
    require(0 <= u && u <= 1)
    (-3 * u*u*u  + 3*u*u + 3*u + 1) * (1.0/6)
  } ensuring (res => -0.02 <= res && res <= 0.89)

  def bspline3(u: Double): Double = {
    require(0 <= u && u <= 1)
    u*u*u * (1.0/6.0)
  } ensuring (res => -0.17 <= res && res <= 0.05)

}
