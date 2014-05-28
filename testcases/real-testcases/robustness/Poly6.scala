import leon.real._
import RealOps._

object SixDegreePolynomial {


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

}