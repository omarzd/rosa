
import leon.Real
import Real._


/*
  Source:
*/
object CAV10 {

  def f(x: Real): Real = {
    require(x.in(0, 10)) // x in [0,10]
    val y = x*x - x
    if (y >= 0) {
      x/10
    } else {
      x*x + 2
    }
  } ensuring(res => 0 <= res && res <= 3.0)
}