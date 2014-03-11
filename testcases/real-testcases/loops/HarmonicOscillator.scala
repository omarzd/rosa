import leon._
import Real._
import RealAnnotations._

object HarmonicOscillator {

  @loopbound(10)
  def euler(x: Real, v: Real): (Real, Real) = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
    iterate (x, v) {
      x <== x + 0.1 * v
      v <== v - 2.3 * 0.1 * x
    }
  } ensuring (_ match {
    case (a, b) => -10 <= a && a <= 10 && -10 <= b && b <= 10   
  })


  def rungeKutta2(x: Real, v: Real): (Real, Real) = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)

    iterate (x, v) {

      val k: Real = 2.3
      val h: Real = 0.1
      
      val dx = h * (v + (-k*x*h/2))
      val dv = h * (-k)* (x + v*h/2)

      x <== x + dx
      v <== v + dv
    }

  } ensuring (_ match {
    case (a, b) => -10 <= a && a <= 10 && -10 <= b && b <= 10   
  })


  def rungeKutta4(x: Real, v: Real): (Real, Real) = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
 
    iterate (x, v) {

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
      
      x <== x + h*(k1x + 2.0*k2x + 2*k3x + k4x)/6.0
      v <== v + h*(k1v + 2.0*k2v + 2*k3v + k4v)/6.0
    }

  } ensuring (_ match {
    case (a, b) => -10 <= a && a <= 10 && -10 <= b && b <= 10   
  })


  // k = 2.3, dt = 0.1
  /*def eulerFor(i: Int, x: Real, v: Real): (Real, Real) = {
    require(-10.0 <= x && x <= 10.0 && -10.0 <= v && v <= 10.0)
    if (i > 1000) {
      (x, v)
    } else {
      val xn = x + 0.1 * v
      val vn = v - 2.3 * 0.1 * x
      eulerFor(i + 1, xn, vn)
    }
  } ensuring (res => x <= 10.0)

  def eulerBack(i: Int, x: Real, v: Real): (Real, Real) = {
    require(-10.0 <= x && x <= 10.0 && -10.0 <= v && v <= 10.0)
    if (i > 1000) {
      (x, v)
    } else {
      val (xn, vn) = eulerBack(i + 1, x, v)
      (xn + 0.1 * vn, vn - 2.3 * 0.1 * xn) 
    }
  } ensuring (res => 10.0 <= x && x <= 10.0 && 10.0 <= v && v <= 10.0)
  */
}