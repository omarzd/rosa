import leon.Real
import Real._

object HarmonicOscillator {


  def euler(x: Real, v: Real): (Real, Real) = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
    iterate {
      val tmp = 0.1 * v
      x <== x + tmp
      v <== v - 2.3 * 0.1 * x
    }
  }


  // k = 2.3, dt = 0.1
  /*def eulerFor(i: Int, x: Real, v: Real): (Real, Real) = {
    require(10.0 <= x && x <= 10.0 && 10.0 <= v && v <= 10.0)
    if (i > 1000) {
      (x, v)
    } else {
      val xn = x + 0.1 * v
      val vn = v - 2.3 * 0.1 * x
      euler(i + 1, xn, vn)
    }
  } ensuring (res => x <= 10.0)

  def eulerBack(i: Int, x: Real, v: Real): (Real, Real) = {
    require(10.0 <= x && x <= 10.0 && 10.0 <= v && v <= 10.0)
    if (i > 1000) {
      (x, v)
    } else {
      val (xn, vn) = euler(i + 1, x, v)
      (xn + 0.1 * vn, vn - 2.3 * 0.1 * xn) 
    }
  } ensuring (res => 10.0 <= x && x <= 10.0 && 10.0 <= v && v <= 10.0)
  */
}