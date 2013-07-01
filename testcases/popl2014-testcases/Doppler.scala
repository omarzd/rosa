
import leon.Real
import Real._

object Doppler {

  def doppler1(u: Real, v: Real, T: Real): Real = {
    require(-100 <= u && u <= 100 && 20 <= v && v <= 20000 &&
     -30 <= T && T <= 50 && noise(u, 1e-7) && noise(v, 1e-9) && noise(T, 1e-6))

    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))

  } ensuring (res => -137.0 <= res && res <= -0.35 && noise(res, 1e-4))

  def doppler2(u: Real, v: Real, T: Real): Real = {
    require(-125 <= u && u <= 125 && 15 <= v && v <= 25000 &&
     -40 <= T && T <= 60 && noise(u, 1e-12) && noise(v, 1e-3) && noise(T, 1e-5))

    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))

  } ensuring (res => -227.5 <= res && res <= -0.05 && noise(res, 1e-12))

  def doppler3(u: Real, v: Real, T: Real): Real = {
    require(-30 <= u && u <= 120 && 320 <= v && v <= 20300 &&
     -50 <= T && T <= 30 && noise(u, 1e-4) && noise(v, 1e-5) && noise(T, 1e-9))

    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))

  } ensuring (res => -82.5 <= res && res <= -0.6 && noise(res, 1e-13))



}