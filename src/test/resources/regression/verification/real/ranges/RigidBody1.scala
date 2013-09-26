import leon.Real
import Real._

object RigidBody1 {

  def rigidBody1(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 >< (-15, 15) && x2 >< (-15, 15) && x3 >< (-15, 15))

    -x1*x2 - 2*x2*x3 - x1 - x3
  }

}