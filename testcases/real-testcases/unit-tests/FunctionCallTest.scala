import leon.Real
import Real._


object FunctionCallTest {

  def inline(x: Real): Real = {
    require(x >< (2, 3))
    x * x
  } ensuring(res => res <= 10)

  def f1(x: Real): Real = {
    require(x >< (3,4))
    val z = 2*x
    inline(z)
  } ensuring(res => res <= 10)
}