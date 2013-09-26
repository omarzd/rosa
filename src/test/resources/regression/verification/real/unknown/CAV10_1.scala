import leon.Real
import Real._

// Tests if-then-else handling
object IfThenElse1 {

  def cav10(x: Real): Real = {
    require(x >< (0, 10))
    if (x*x - x >= 0)
      x/10
    else 
      x*x + 2
    // TODO: path error
  } ensuring(res => 0.1 <= res && res <= 3.0)

}