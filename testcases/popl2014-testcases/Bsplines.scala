
import leon.Real
import Real._

/**
  Equation and initial ranges from:
  L. Zhang, Y. Zhang, and W. Zhou. Tradeoff between Approximation Accuracy and
  Complexity for Range Analysis using Affine Arithmetic.
*/
object Bsplines {

  def bspline3(u: Real): Real = {
    require(0 < u && u < 1 && u +/- 1e-13)
    -u*u*u / 6.0
  } ensuring (res => -0.17 <= res && res <= 0.05 && res +/- 1e-11)

}
