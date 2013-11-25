import leon.Real
import Real._


object Arithmetic2 {

  def f(x: Real): Real = {
    require(x >< (1.0, 2.0) && x +/- 1e-9)
    x * x
  } ensuring (res => ~res <= 4.0001 && res +/- 1e-8)
}