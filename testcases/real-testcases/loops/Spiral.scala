import leon.Real
import Real._

object Spiral {

  def step(x: Real, y: Real, k: Real): (Real, Real) = {
    require(0 <= k && k <= 10 && x*x + y*y < 100 && -10 <= x && x <= 10 &&
            -10 <= y && y <= 10)
    
    // k should be an integer
    if (k > 1.1) {
      val x1 = (9.9*x - y)/10
      val y1 = (9.9*y + x)/10
      step(x1,y1,k-1)
    } else {
      (x, y)
    }

  } ensuring (_ match {
    case (a, b) => 0 <= a && a < 100 && 0 <= b && b < 100 //&& a +/- 1e-12 && b +/- 1e-12
  })