import leon.Real
import Real._

object Ellipsoid {

  /*def main {

    step(9.95, 0.0, 10)

  // how do we ensure the error bound, when the postcondition only talks about ~res?
  // to really get that error bound, we'd need to track the error through all computations
  // with our current technique.
  } ensuring( res => res +/- 1e-12)
  */


  // We don't have Tuples or Ints, so we return x*x + y*y
  def step(x: Real, y: Real, k: Real): Real = {
    require(0 <= k && k <= 10 && x*x + y*y < 100 && - 10 <= x && x <= 10 &&
       -10 <= y && y <= 10)
    
    // greater than one, since k should be an integer, but we don't support that yet
    if (k > 1) {
      val x1 = (9*x - y)/10
      val y1 = (9*y + x)/10
      step(x1,y1,k-1)
    } else {
      x*x + y*y
    }

  } ensuring(res => 0 <= ~res && ~res < 100 && res +/- 1e-12) // && res +/- 1e-12)  
}