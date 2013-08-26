import leon.Real
import Real._


object FunctionCallTest {

  def inline(a: Real): Real = {
    require(a >< (2, 3))
    a * a
  } ensuring(res => res <= 10 && res >= -1 && res +/- 1e-6)

  def f1(x: Real): Real = {
    require(x >< (3,4))
    val z = if (x < 0) 2*x else 3*x
    if (z > 3) inline(z)
    else inline(2)
  } ensuring(res => res <= 10)

  /*def f1(x: Real): Real = {
    require(x >< (3,4))
    val z = 2*x
    val w = inline(z) + 2.0
    3.4 * w
  } ensuring(res => res <= 10)
  */
}