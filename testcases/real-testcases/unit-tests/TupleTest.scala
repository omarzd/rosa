import leon.Real
import Real._


object TupleTest {

  def tuple(x: Real, y: Real): (Real, Real) = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    (x * x, x + y)
  }
  
}