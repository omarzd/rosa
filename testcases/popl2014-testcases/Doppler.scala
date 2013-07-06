
import leon.Real
import Real._

object Doppler {


  def doppler1(u: Real, v: Real, T: Real): Real = {
    require(u.in(-100, 100) && v.in(20, 20000) && T.in(-30, 50) && u +/- 1e-7 && v +/- 1e-9 && T +/- 1e-6)

    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))

  }

  def doppler2(u: Real, v: Real, T: Real): Real = {
    require(u.in(-125, 125) && v.in(15, 25000) && T.in(-40, 60) && u +/- 1e-12 && v +/- 1e-3 && T +/- 1e-5)

    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))

  }

  def doppler3(u: Real, v: Real, T: Real): Real = {
    require(u.in(-30, 120) && v.in(320, 20300) && T.in(-50, 30) && u +/- 1e-4 && v +/- 1e-5 && T +/- 1e-9)

    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))

  }

}