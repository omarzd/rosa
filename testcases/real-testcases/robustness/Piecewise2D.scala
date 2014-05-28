import leon.real._
import RealOps._

object Piecewise2D {

  // looking at the picture, the error should be about ~1.0
  def linear(x: Real, y: Real): Real = {
    require(-4 <= x && x <= 4 && -4 <= y && y <= 4)


    if (x <= 0) {

      if (y <= 0) {

        -0.495356 - 0.123839*x - 0.1233839*y        

      } else {

        0.495356 + 0.123839*x - 0.1233839*y        

      }


    } else { // x >= 0

      if (y <= 0) {

        0.495356 - 0.123839*x + 0.1233839*y        

      } else {

        -0.495356 + 0.123839*x + 0.1233839*y

      }

    }

  } ensuring ( res => res +/- 1e-9 )

}
