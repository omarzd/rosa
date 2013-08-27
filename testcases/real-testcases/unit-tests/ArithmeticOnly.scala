import leon.Real
import Real._


object ArithmeticOnly {

  def f1_simple(x: Real): Real = {
    require(x >< (1.0, 2.0) && x +/- 1e-9)
    
    x * x
  } ensuring (res => res <= 5.0 && res +/- 1e-8)

  def f2_simple(x: Real): Real = {
    require(x >< (1.0, 2.0) && x +/- 1e-5)

    x * x
  } ensuring (res => res <= 3.0)


  def f1_noNoise(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    x * (sqrt(x) - y) / x + (-x)
  } ensuring (res => res <= 0)

  def f2_noNoise(x: Real, y: Real): Real = {
    require(-2.2 <= x && x <= 2.3 && 3.5 <= y && y <= 7.5)
    x * (sqrt(x) - y) / x + (-x)
  } ensuring (res => res <= 0.0)


  def f1_withNoise(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5) && x +/- 1e-5 && y +/- 1e-7)
    x * (sqrt(x) - y) / x + (-x)
  } ensuring (res => res <= 0 && res +/- 1e-6)

  def f2_withNoise(x: Real, y: Real): Real = {
    require(-2.2 <= x && x <= 2.3 && 3.5 <= y && y <= 7.5 && x +/- 1e-5) // y has roundoff
    x * (sqrt(x) - y) / x + (-x)
  } ensuring (res => res >< (-5, 7.5),  && res +/- 1e-4)


  def f1_actual(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5) && x +/- 1e-5 && y +/- 1e-7)
    x * (sqrt(x) - y) / x + (-x)
  } ensuring (res => ~res <= 0 && res +/- 1e-6)

  def f2_actual(x: Real, y: Real): Real = {
    require(-2.2 <= x && x <= 2.3 && 3.5 <= y && y <= 7.5 && x +/- 1e-5) // y has roundoff
    x * (sqrt(x) - y) / x + (-x)
  } ensuring (res => ~res >< (-5.001, 7) && res +/- 1e-4)


  def f1_cnstr(x: Real, y: Real): Real = {
    require(x >< (2.0, 3.5) && y >< (2.0, 3.5) && x <= y)
    x * (sqrt(x) - y) / x + (-x)
  } ensuring (res => res <= 0)

  def f2_cnstr(x: Real, y: Real): Real = {
    require(-2.2 <= x && x <= 2.3 && 3.5 <= y && y <= 7.5 && 3 * x >= y)
    x * (sqrt(x) - y) / x + (-x)
  } ensuring (res => res <= 0.0)


  // Errors we should catch
  def xints(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    x * x + (3 + 4)
  }

  def xnoiseOnActual(x: Real, y: Real): Real = {
    require(-2.2 <= x && x <= 2.3 && 3.5 <= y && y <= 7.5 && x +/- 1e-5) // y has roundoff
    x * (sqrt(x) - y) / x + (-x)
  } ensuring (res => ~res +/- 1e-4)


  def xinvalidIntervalComparisons(x: Real, y: Real): Real = {
    require(-2.2 <= x && x <= -2.3 && 3.5 <= y && y <= 7.5)
    x + y
  }

  def xunBounded(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3))
    x + y
  }

  def xunBounded2(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y <= 3.3)
    x + y
  }

}
