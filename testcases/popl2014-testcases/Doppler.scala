
import leon.Real
import Real._

object Doppler {


  def doppler1(u: Real, v: Real, T: Real): Real = {
    require(u.in(-100, 100) && v.in(20, 20000) && T.in(-30, 50) &&
      noise(u, 1e-7) && noise(v, 1e-9) && noise(T, 1e-6))

    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))

  } ensuring (res => -137.0 <= res && res <= -0.35 && noise(res, 1e-4))

  def doppler2(u: Real, v: Real, T: Real): Real = {
    require(u.in(-125, 125) && v.in(15, 25000) && T.in(-40, 60) &&
      noise(u, 1e-12) && noise(v, 1e-3) && noise(T, 1e-5))

    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))

  } ensuring (res => -227.5 < res && res < -0.05 && noise(res, 1e-12))

  def doppler3(u: Real, v: Real, T: Real): Real = {
    require(u.in(-30, 120) && v.in(320, 20300) && T.in(-50, 30) &&
      noise(u, 1e-4) && noise(v, 1e-5) && noise(T, 1e-9))

    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))

  } ensuring (res => -82.5 <= res && res <= -0.6 && noise(res, 1e-13))


}