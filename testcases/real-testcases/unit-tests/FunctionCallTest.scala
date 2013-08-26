import leon.Real
import Real._


object FunctionCallTest {

  def inline(a: Real): Real = {
    require(a >< (2, 3))
    a * a
  } ensuring(res => res <= 10 && res >= -1 && res +/- 1e-6)

  def f1(x: Real): Real = {
    require(x >< (3,4))
    val z = 2*x
    inline(z)
  } ensuring(res => res <= 10)

  /*def f1(x: Real): Real = {
    require(x >< (3,4))
    val z = 2*x
    val w = inline(z) + 2.0
    3.4 * w
  } ensuring(res => res <= 10)
  */
}