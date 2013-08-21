import leon.Real
import Real._


object Z3Test {


  def f1True(x: Real): Real = {
    require(x >< (1.0, 2.0) && x +/- 1e-9)

    x * x
  }// ensuring (res => res <= 5.0 && res +/- 1e-8)

  def f1False(x: Real): Real = {
    require(x >< (1.0, 2.0))

    x * x
  } ensuring (res => res <= 3.0)

  def f2True(x: Real): Real = {
    require(x >< (1.0, 2.0) && x +/- 1e-9)

    x * x
  } ensuring (res => res <= 5.0 && res +/- 1e-8)

}