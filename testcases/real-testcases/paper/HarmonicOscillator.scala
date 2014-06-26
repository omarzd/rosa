import leon.real._
import RealOps._
import annotations._

object HarmonicOscillator {

  def rk2(x: Real, v: Real, i: LoopCounter): (Real, Real) = {
    require(-15.0 <= x && x <= 15.0 && -20.0 <= v && v <= 20.0 &&
            -15.0 <= ~x && ~x <= 15.0 && -20.0 <= ~v && ~v <= 20.0)

    if (i < 300) {
      val k: Real = 2.3
      val h: Real = 0.1
      
      val dx = h * (v + (-k*x*h/2))
      val dv = h * (-k)* (x + v*h/2)

      rk2(x + dx, v + dv, i++)
    } else {
      (x, v)
    }

  } ensuring (_ match {
    case (a, b) => -10 <= a && a <= 10 && -10 <= b && b <= 10// &&
      //a +/- 3e-14 && b +/- 3.4e-14
  }) 

  def rk4(x: Real, v: Real, i: LoopCounter): (Real, Real) = {
    require(-15.0 <= x && x <= 15.0 && -20.0 <= v && v <= 20.0 &&
            -15.0 <= ~x && ~x <= 15.0 && -20.0 <= ~v && ~v <= 20.0)
 
    if (i < 300) {

      val k: Real = 2.3
      val h: Real = 0.1

      val k1x = v
      val k1v = -k*x

      val k2x = v - k*h*x/2.0
      val k2v = -k*x - h*k*v/2.0

      val k3x = v - k*h*x/2.0 - h*h*k*v/4.0
      val k3v = -k*x - k*h*v/2.0 + k*k*h*h*x/4.0

      val k4x = v - k*h*x - k*h*h*v/2.0 + k*k*h*h*h*x/4.0
      val k4v = -k*x - k*h*v + k*k*h*h*x/2.0 + h*h*h*k*k*v/4.0
      
      val x1 = x + h*(k1x + 2.0*k2x + 2*k3x + k4x)/6.0
      val v1 = v + h*(k1v + 2.0*k2v + 2*k3v + k4v)/6.0

      rk4(x1, v1, i++)

    } else {
      (x, v)
    }

  } ensuring (_ match {
    case (a, b) => -10 <= a && a <= 10 && -10 <= b && b <= 10// &&
      //a +/- 3e-14 && b +/- 3.4e-14
  }) 
}