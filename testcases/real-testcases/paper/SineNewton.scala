import leon.real._
import RealOps._
import annotations._

object SineNewton {


  def newton(x: Real, k: LoopCounter): Real = {
    require(-1.0 < x && x < 1.0 && -1.0 < ~x && ~x < 1.0)

    if (k < 10) {
      newton(x - (x - (x°°3)/6.0 + (x°°5)/120.0 + (x°°7)/5040.0) / 
        (1.0 - (x*x)/2.0 + (x°°4)/24.0 + (x°°6)/720.0), k++)
    } else {
      x
    }
    
  } ensuring(res => -1.0 < res && res < 1.0 && -1.0 < ~res && ~res < 1.0)

  def newton2(x: Real, k: LoopCounter): Real = {
    require(-1.2 < x && x < 1.2 && -1.2 < ~x && ~x < 1.2)

    if (k < 10) {
      newton2(x - (x - (x°°3)/6.0 + (x°°5)/120.0 + (x°°7)/5040.0) / 
        (1.0 - (x*x)/2.0 + (x°°4)/24.0 + (x°°6)/720.0), k++)
    } else {
      x
    }
    
  } ensuring(res => -1.2 < res && res < 1.2 && -1.2 < ~res && ~res < 1.2)

}