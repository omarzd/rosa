
import leon.Real
import Real._


object Test {

  /* Vary the result error to test different precisions
  def bspline0(u: Real): Real = {
    require(0 <= u && u <= 1)
    (1 - u) * (1 - u) * (1 - u) / 6.0
  } ensuring (res => 0 <= res && res <= 0.17 && res +/- 1e-19)

  */

  def jetEngine(x1: Real, x2: Real): Real = {
    require(x1 >< (-5, 5) && x2 >< (-20, 5))

    val t = (3*x1*x1 + 2*x2 - x1)

    x1 + ((2*x1*(t/(x1*x1 + 1))*
    (t/(x1*x1 + 1) - 3) + x1*x1*(4*(t/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(t/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  } ensuring (res => -1997.1 <= res && res <= 5109.4 && res +/- 1.62e-8)
//[-1997.036793449632, 5109.337370948639  1.6170398214864217e-08
}
