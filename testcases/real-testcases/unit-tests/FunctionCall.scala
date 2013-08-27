import leon.Real
import Real._


object FunctionCalls {

  // TODO: if the method does not specify the error in the precondition?

  def mult(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    x * y
  }

  def quad(a: Real): Real = {
    require(a >< (2, 3))
    a * a
  } ensuring(res => res <= 10 && res >= -1 && res +/- 1e-6)

  def f1(x: Real): Real = {
    require(x >< (3,4))
    val z = if (x < 3.5) 2*x else 3*x
    if (z > 3) quad(z)
    else quad(2)
  } ensuring(res => res <= 10)


  def functionCall(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    mult(x * x, y * y)
  } ensuring(res => res +/- 1e-7)

  /*def f1(x: Real): Real = {
    require(x >< (3,4))
    val z = 2*x
    val w = inline(z) + 2.0
    3.4 * w
  } ensuring(res => res <= 10)
  */
}