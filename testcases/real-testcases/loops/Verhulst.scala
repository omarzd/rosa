import leon.Real
import Real._

object Verhulst {
  val r: Real = ???  // 1/r timescale at which K is reached
  val K: Real = 45.0 // carrying capacity
  val dt: Real = 0.1

  def next(n: Real, t: Real): Real = {
    require(0.0 <= n && n <= 50.0)
    if (t < tMax) {
      n + dt * (r * n * (1.0 - n/K))
    } else {
      n
    }
  }

}
