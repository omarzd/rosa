/* Copyright 2009-2015 EPFL, Lausanne */

import RealOps._

object DopplerApproxUnknown {

  def doppler1Star(u: Real, v: Real, T: Real): Real = {
    require(-100.0 < u && u < 100 && 20 < v && v < 20000 && -30 < T && T < 50 &&
      u +/- 1e-7 && v +/- 1e-9 && T +/- 1e-6)
    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))
  } ensuring(res => -137.63858 < res && res < -0.03394 && res +/- 2.3547e-6)

  def doppler1(u: Real, v: Real, T: Real): Real = {
    require(-100.0 <= u && u <= 100 && 20 <= v && v <= 20000 && -30 <= T && T <= 50)
    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))
  } ensuring(res => -137.63858 < res && res < -0.03394 && res +/- 4.1911e-13)

  def doppler2Star(u: Real, v: Real, T: Real): Real = {
    require(-125.0 <= u && u <= 125.0 && 15.0 <= v && v <= 25000 && -40 <= T && T <= 60 &&
      u +/- 1e-12 && v +/- 1e-3 && T +/- 1e-5)
    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))
  } ensuring(res => -230.990546 < res && res < -0.0227296 && res +/- 6.201846e-5)

  def doppler2(u: Real, v: Real, T: Real): Real = {
    require(-125.0 <= u && u <= 125.0 && 15.0 <= v && v <= 25000 && -40 <= T && T <= 60)
    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))
  } ensuring(res => -230.990546 < res && res < -0.0227296 && res +/- 1.03289e-12)

  def doppler3Star(u: Real, v: Real, T: Real): Real = {
    require(-30 <= u && u <= 120 && 320.0 <= v && v <= 20300 && -50 <= T && T <= 30 &&
      u +/- 1e-4 && v +/- 1e-5 && T +/- 1e-9)
    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))
  } ensuring(res => -83.0653 < res && res < -0.507441 && res +/- 0.0001227)

  def doppler3(u: Real, v: Real, T: Real): Real = {
    require(-30 <= u && u <= 120 && 320.0 <= v && v <= 20300 && -50 <= T && T <= 30)
    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))
  } ensuring(res => -83.06530 < res && res < -0.507441 && res +/- 1.68292e-13)
}