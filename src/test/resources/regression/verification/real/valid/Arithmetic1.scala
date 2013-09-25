import leon.Real
import Real._


object Arithmetic1 {

  // valid
  def f(x: Real): Real = {
    require(x >< (1.0, 2.0) && x +/- 1e-9)
    x * x
  } ensuring (res => res <= 4.1 && res +/- 1e-8)
}