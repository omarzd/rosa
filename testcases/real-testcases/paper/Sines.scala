import leon.real._
import RealOps._
import annotations._

object Testing {

  def sineTaylor(x: Real): Real = {
    require(-3.5 < x && x < 3.5 && x +/- 1e-8)

    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 - (x*x*x*x*x*x*x)/5040.0 
  } ensuring(res => -1.0 < ~res && ~res < 1.0 && res +/- 2e-7)


  def test(y: Real): Real = {
    require(-0.5 <= y && y <= 0.5 && y +/- 1e-8)

      y * sineTaylor(y)

  } ensuring(res => res +/- 1e-15)

  def test2(y: Real): Real = {
    require(-3.0 <= y && y <= 1)

      y * sineTaylor(y)

  } ensuring(res => res +/- 1e-14)
  

}