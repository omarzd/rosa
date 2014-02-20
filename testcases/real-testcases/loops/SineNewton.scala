import leon.Real
import Real._

object SineNewton {

  def newton(x: Real, i: Int): Real = {
    require(-1.0 < x && x < 1.0)

    if (i < 10) {
      newton(x - (x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0) / 
        (1 - (x*x)/2.0 + (x*x*x*x)/24.0 + (x*x*x*x*x*x)/720.0), i + 1)
    } else {
      x
    }
    
  } ensuring(res => -1.0 < x && x < 1.0)  // has not diverged
  // This condition could probably be even stronger, something like 
  // ensuring( res => res < 0.1 * x)

  def newton2(x: Real): Real = {
    require(-1.2 < x && x < 1.2)

    if (i < 10) {
      newton2(x - (x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0) / 
        (1 - (x*x)/2.0 + (x*x*x*x)/24.0 + (x*x*x*x*x*x)/720.0), i + 1)
    } else {
      x
    }
    
  } ensuring(res => -1.0 < x && x < 1.0)  // diverges (in some cases)!

}