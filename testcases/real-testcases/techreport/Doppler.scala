
import leon.Real
import Real._

object Doppler {


  def doppler1(u: Real, v: Real, T: Real): Real = {
    require(u >< (-100, 100) && v >< (20, 20000) && T >< (-30, 50) && u +/- 1e-7 && v +/- 1e-9 && T +/- 1e-6)
    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))
  }

  def doppler2(u: Real, v: Real, T: Real): Real = {
    require(u >< (-125, 125) && v >< (15, 25000) && T >< (-40, 60) && u +/- 1e-12 && v +/- 1e-3 && T +/- 1e-5)
    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))
  }

  def doppler3(u: Real, v: Real, T: Real): Real = {
    require(u >< (-30, 120) && v >< (320, 20300) && T >< (-50, 30) && u +/- 1e-4 && v +/- 1e-5 && T +/- 1e-9)
    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))
  }


  def doppler1_roundoff(u: Real, v: Real, T: Real): Real = {
    require(u >< (-100, 100) && v >< (20, 20000) && T >< (-30, 50))
    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))
  }

  def doppler2_roundoff(u: Real, v: Real, T: Real): Real = {
    require(u >< (-125, 125) && v >< (15, 25000) && T >< (-40, 60))
    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))
  }

  def doppler3_roundoff(u: Real, v: Real, T: Real): Real = {
    require(u >< (-30, 120) && v >< (320, 20300) && T >< (-50, 30))
    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))
  }

}