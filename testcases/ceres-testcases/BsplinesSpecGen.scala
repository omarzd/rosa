
import leon.Real
import Real._

/**
  Equations and initial ranges from:
  L. Zhang, Y. Zhang, and W. Zhou. Tradeoff between Approximation Accuracy and
  Complexity for Range Analysis using Affine Arithmetic.
*/
object BsplinesSpecGen {

  // TODO: it should be 1/6 throughout, but we cannot handle that atm.

  def bspline0(u: Real): Real = {
    require(0 <= u && u <= 1 && roundoff(u))
    ((1 - u) * (1 - u) * (1 - u)) / 6.0  //* 0.1666666
  }

  def bspline1(u: Real): Real = {
    require(0 <= u && u <= 1 && roundoff(u))
    (3 * u*u*u - 6 * u*u + 4) / 6.0  //* 0.1666666
  }

  def bspline2(u: Real): Real = {
    require(0 <= u && u <= 1 && roundoff(u))
    (-3 * u*u*u  + 3*u*u + 3*u + 1) / 6.0  // * 0.1666666
  }

  def bspline3(u: Real): Real = {
    require(0 <= u && u <= 1 && roundoff(u))
    (-u*u*u ) / 6.0  //* 0.1666666
  }

}
