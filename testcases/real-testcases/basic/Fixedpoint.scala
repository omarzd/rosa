
import leon.real._
import RealOps._

/* From:
  To Sample or not to Sample: Self-Triggered Control for Nonlinear Systems,
  Anta, Adolfo and Tabuada, P.
*/
object Fixedpoint {

  def rigidBody1(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 >< (-15, 15) && x2 >< (-15, 15) && x3 >< (-15, 15) && x1 +/- 1e-8 && x2 +/- 1e-8 && x3 +/- 1e-8)

    -x1*x2 - 2*x2*x3 - x1 - x3
  }

  def rigidBody1_roundoff(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 >< (-15, 15) && x2 >< (-15, 15) && x3 >< (-15, 15))

    -x1*x2 - 2*x2*x3 - x1 - x3
  }

  def rigidBody2(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 >< (-15, 15) && x2 >< (-15, 15) && x3 >< (-15, 15) && x1 +/- 1e-8 && x2 +/- 1e-8 && x3 +/- 1e-8)

    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  }

  def rigidBody2_roundoff(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 >< (-15, 15) && x2 >< (-15, 15) && x3 >< (-15, 15))

    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  }

  def jetEngine(x1: Real, x2: Real): Real = {
    require(x1 >< (-5, 5) && x2 >< (-20, 5) && x1 +/- 1e-8 && x2 +/- 1e-8)

    val t = (3*x1*x1 + 2*x2 - x1)

    x1 + ((2*x1*(t/(x1*x1 + 1))*
    (t/(x1*x1 + 1) - 3) + x1*x1*(4*(t/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(t/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  }

  def jetEngine_roundoff(x1: Real, x2: Real): Real = {
    require(x1 >< (-5, 5) && x2 >< (-20, 5))

    val t = (3*x1*x1 + 2*x2 - x1)

    x1 + ((2*x1*(t/(x1*x1 + 1))*
    (t/(x1*x1 + 1) - 3) + x1*x1*(4*(t/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(t/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  }

}
