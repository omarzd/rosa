import leon.Real
import Real._

object Ellipsoid {

  // We don't have Tuples or Ints, so we return x*x + y*y
  def f(x: Real, y: Real, k: Real) : Real = {
    require(k >= 0 && x*x + y*y < 100)
    if (k > 0) {
      val x1 = (9*x - y)/10
      val y1 = (9*y + x)/10
      f(x1,y1,k-1)
    } else x*x + y*y
  } ensuring(res => res < 100)

  // Original formulation
  /*def f(x: Real, y: Real, k: Int) : (Real, Real) = {
    require(k >= 0 && x*x + y*y < 100)
    if (k > 0) {
      val x1 = (9*x - y)/10
      val y1 = (9*y + x)/10
      f(x1,y1,k-1)
    } else (x,y)
  } ensuring(res => res._1 * res._1 + res._2 * res._2 < 100)
  */  
}