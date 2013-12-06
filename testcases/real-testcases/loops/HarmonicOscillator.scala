import leon.Real
import Real._


object HarmonicOscillator {

  // TODO: E = 0.5 * m * v*v
  // U = 0.5 * k * x*x

  val dt = 0.05
  val until = 1.0
  val k = 1.0 // spring constant, sort of

   // 1.0 is the max amplitude
   // the max potential energy is U = 0.5 * k *x*x = 0.5 * (1.0)^2 = 0.5
   // let m = 1
  def eulerSpring(x: Real, v: Real, t: Real): Real = {
    require(0 <= x && x < 1.0 && 0 <= t && t <= until && v ???  && 
      // this equality will be problematic, maybe we just require that this is bounded above
      // and/or below?
      0.5 = (0.5 * x*x) + (0.5 * v*v))

    if (t >= until) {
      x
    } else {
      eulerSpring(x + v*dt, v + (-k*x*dt), t + dt)
    }
  } ensuring (res => res <= 1.0)  // don't diverge

  def rk2Spring(x: Real, v: Real, t: Real): Real = {
    // same as above

    if (t >= until) {
      x
    } else {
      val dx = dt * (v + (-k*x*dt/2))
      val dv = dt * (-k)* (x + v*dt/2)
      rk2Spring(x + dx, v + dv, t + dt)
    }
  } ensuring (res => res <= 1.0)  // don't diverge

}