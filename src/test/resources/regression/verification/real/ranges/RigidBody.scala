import leon.Real
import Real._

object RigidBody {

  def rigidBody1Star(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 >< (-15, 15) && x2 >< (-15, 15) && x3 >< (-15, 15) && x1 +/- 1e-8 && x2 +/- 1e-8 && x3 +/- 1e-8)
    -x1*x2 - 2*x2*x3 - x1 - x3
  }

  def rigidBody1(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 >< (-15, 15) && x2 >< (-15, 15) && x3 >< (-15, 15))

    -x1*x2 - 2*x2*x3 - x1 - x3
  }

  def rigidBody2Star(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 >< (-15, 15) && x2 >< (-15, 15) && x3 >< (-15, 15) && x1 +/- 1e-8 && x2 +/- 1e-8 && x3 +/- 1e-8)

    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  }

  def rigidBody2(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 >< (-15, 15) && x2 >< (-15, 15) && x3 >< (-15, 15))

    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  }


}