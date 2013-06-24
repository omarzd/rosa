import leon.Real
import Real._



object ToughOnes {

  def beales(x: Real, y: Real): Real = {
    require(-4 < x && x < 0.5 && 1.5 < y && y < 4.45 && roundoff(x) && roundoff(y))
    (1.5 - x + x*y)*(1.5 - x + x*y) +
    (2.25 - x + x*y*(x*y))*(2.25 - x + x*y*(x*y)) +
    (2.625 - x + x*y*(x*y)*(x*y))*(2.625 - x + x*y*(x*y)*(x*y))
  } ensuring (res => 13.0 <= res && res <= 31629067.0 && noise(res, 1e-7))

  def jetEngine(x1: Real, x2: Real): Real = {
    require(-5 < x1 && x1 < 5 && -20 < x2 && x2 < 5 && roundoff(x1) && roundoff(x2))
    x1 + ((2*x1*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1))*
    ((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1) - 3) + x1*x1*(4*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  } ensuring (res => -2500.0 <= res && res >= 5500.0 && noise(res, 1e-10))

  def goldstein(x: Real, y: Real): Real = {
    require(-1.5 < x && x < 0.5 && 0.5 < y && y < 1.5 && roundoff(x, y))
    (1 + (x + y + 1)*(x + y + 1) *(19 - 14*x + 3*x*x - 14*y + 6*x*y + 3*y*y)) *
    (30 + (2*x - 3*y)*(2*x - 3*y) * (18 - 32*x + 12*x*x +48*y - 36*x*y + 27*y*y))
  } ensuring (res => res >= -56020.0)
  

  def doppler0(u: Real, v: Real, T: Real): Real = {
    require(-100 < u && u < 100 && 20 < v && v < 20000 &&
     -30 <= T && T <= 50 && roundoff(u, v, T))
    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))
  } ensuring (res => -137.0 <= res && res <= -0.35 && noise(res, 1e-4))

}