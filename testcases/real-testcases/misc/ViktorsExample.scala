import leon.Real
import Real._

object ViktorsExample {

  def test(k: Real, x: Real): Real = {
    require(0.0 < k && k <= 10.0 && 1.0 < x && x > 1.0)

    if (k > 0) {
      // x grows. this is going to be problematic, as we need to satisfy the postcondition
      test(k - 1, x + 0.25) + 0.5
    } else {
      x
    }
  } ensuring (res => res <= 100.0)

}