import leon.real._
import RealOps._

object SixDegreePolynomial {

  // the polynomial is constructed as an interpolating polynomial from the points
  // (0, 2.5), (1,0.5), (2, 0.5), (2.5, 1.5), (3, 1.5), (3.5, 1.125), (4, 0)
  // 2.5 + 20.4155x - 53.8966x^2 + 46.8393x^3 -18.6002x^4 + 3.49524x^5 - 0.253175x^6


  def linearApprox(x: Real): Real = {
    require(0 <= x && x <= 4)

    if (x <= 1) {

      -2*x + 2.5

    } else if (x <= 2) {

      val res: Real = 0.5
      res

    } else if (x <= 2.5) {

      2*x - 3.5

    } else if (x <= 3) {

      val res: Real = 1.5
      res

    } else if (x <= 3.5) {

      -0.75*x + 3.75

    } else { // x <= 4

      -2.25*x + 9.0

    }

  } ensuring(res => res +/- 1e-14)


  def quadraticApprox(x: Real): Real = {
    require(0 <= x && x <= 4)

    if (x <= 2) {

      x*x - 3*x + 2.5

    } else if (x <= 3) {

      -2*x*x + 11*x - 13.5

    } else {  // x <= 4

      -1.5*x*x + 9*x - 12.0

    }

  } ensuring(res => res +/- 3e-14)

  def approx(x: Real): Real = {
    require(0 <= x && x <= 4 && x +/- 1e-8)

    if (x <= 2) {
      10.0268 - 14.4554*x + 4.92857*x*x
    } else {
      -4.125 + 4.125*x -0.75*x*x
    }
  }
}