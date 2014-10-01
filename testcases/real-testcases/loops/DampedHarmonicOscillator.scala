import leon.real._
import RealOps._
import annotations._

object DampedHarmonicOscillator {

  //m = 1, k = 2.3 => w = sqrt(2.3)
  @loopbound(10)
  def eulerRec(x: Real, v: Real, i: Int): (Real, Real) = {
    require(loopCounter(i) && -10.0 <= x && x <= 10.0 && -10.0 <= v && v <= 10.0)// &&
      //0.5*(v*v + 2.3*x*x) <= 115)
    
    if (i < 100) {
      val xNext = x + 0.1 * v
      val vNext = v - 0.1 * (2.3 * x + damp * sqrt(2.3) * v)
      eulerRec(xNext, vNext, i + 1)
    } else {
      (x, v)
    }
  } ensuring (_ match {
    case (a, b) => -10 <= a && a <= 10 && -10 <= b && b <= 10   
  })
}