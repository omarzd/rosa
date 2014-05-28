import leon.real._
import RealOps._
import annotations._

object Misc {

  
  def cav10(x: Real): Real = {
    require(0 < x && x < 10)
    if (x*x - x >= 0)
      x/10
    else 
      x*x + 2
  } ensuring(res => 0 <= res && res <= 3.0 && res +/- 3.0)
  
  
}
