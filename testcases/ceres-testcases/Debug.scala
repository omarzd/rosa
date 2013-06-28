


import leon.Real
import Real._



object Debug {

  def doppler(u: Real, v: Real, T: Real): Real = {
    require(-100 <= u && u <= 100 && 20 <= v && v <= 20000 &&
     -30 <= T && T <= 50 && noise(u, 1e-7) && noise(v, 1e-9) && noise(T, 1e-6))

    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))

  } ensuring (res => -138.0 <= res && res <= -0.35 && noise(res, 1e-4))


  def doppler0(u: Real, v: Real, T: Real): Real = {
    require(-100 <= u && u <= 100 && 20 <= v && v <= 20000 &&
     -30 <= T && T <= 50 && roundoff(u, v, T))
    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))
  }

  def doppler1(u: Real, v: Real, T: Real): Real = {
    require(-100 <= u && u <= 100 && 20 <= v && v <= 20000 &&
     -30 <= T && T <= 50 && roundoff(u, v, T))
    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))
  } ensuring (res => -400.0 <= res && res <= 200.0 && noise(res, 1e-5))

}
