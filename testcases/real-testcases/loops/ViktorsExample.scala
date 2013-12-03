import leon.Real
import Real._

object ViktorsExample {

  def test(k: Int, x: Real): Real = {
    require(x > 1.0)

    if (k > 0) {
      test(k-1, x + 0.25) + 0.5
    } else {
      x
    }
  }

}