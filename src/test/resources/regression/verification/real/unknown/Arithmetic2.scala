import leon.Real
import Real._


object Arithmetic1 {

  def f(x: Real): Real = {
    require(x >< (1.0, 2.1))
    x * x * x
  } ensuring (res => ~res <= 9.261)
}