import leon.real._
import RealOps._

object IrwinHallDistribution {

  def cubicSpline(x: Real): Real = {
    require(-2 <= x && x <= 2)

    if (x <= -1) {
      0.25 * (x + 2)* (x + 2)* (x + 2)
    } else if (x <= 0) {
      0.25*(-3*x*x*x - 6*x*x +4)
    } else if (x <= 1) {
      0.25*(3*x*x*x - 6*x*x +4)
    } else if (x <= 2) {
      0.25*(2 - x)*(2 - x)*(2 - x)
    }

  }



}