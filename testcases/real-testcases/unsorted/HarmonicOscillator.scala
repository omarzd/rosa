import leon.Real
import Real._


object HarmonicOscillator {

  // TODO: E = 0.5 * m * v*v
  // U = 0.5 * k * x*x

  val dt = 0.05
  val until = 1.0
  val k = 1.0 // spring constant, sort of

  def eulerSpring(x: Real, v: Real, t: Real): Real = {
    require(x = (0, 1.0) && t <= until && v = (??))   // 1.0 is the max amplitude
    if (t >= until) {
      x
    } else {
      eulerSpring(x + v*dt, v + (-k*x*dt), t + dt)
    }
  }

  def rk2Spring(x: Real, v: Real, t: Real): Real = {
    require(x = (0, 1.0) && t <= until && v = (??))   // 1.0 is the max amplitude
    if (t >= until) {
      x
    } else {
      val dx = dt * (v + (-k*x*dt/2))
      val dv = dt * (-k)* (x + v*dt/2)
      rk2Spring(x + dx, v + dv, t + dt)
    }
  }

}