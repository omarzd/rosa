import leon.Real
import Real._

  // E = 0.5 * m * v*v
  // U = 0.5 * k * x*x

object HarmonicOscillator {

  /* energy of the system: U = 0.5 * k *x*x = 0.5 * (1.0)^2 = 0.5  with  m = 1
     we require that the energy stays bounded
     ~> we may need more precision by doing something like:
     (0.5 * x*x) + (0.5 * v*v) \in [0.5 +/- tol]
      strict equality won't hold
   */
  def eulerSpring(x: Real, v: Real, t: Real): Real = {
    require(0 <= x && x <= 1.0 && 0 <= t && t <= 1.0 && 0 <= v && v <= 1.0 && 
      (0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 1.0 // spring constant
    val dt = 0.05 // step size

    if (t >= until) {
      x
    } else {
      eulerSpring(x + v*dt, v + (-k*x*dt), t + dt)
    }
  } ensuring (res => res <= 1.0)  // don't diverge


  def rk2Spring(x: Real, v: Real, t: Real): Real = {
    require(0 <= x && x <= 1.0 && 0 <= t && t <= 1.0 && 0 <= v && v <= 1.0 && 
      (0.5 * x*x) + (0.5 * v*v) <= 0.5)
   
    val k = 1.0 // spring constant 
    if (t >= until) {
      x
    } else {
      val dx = dt * (v + (-k*x*dt/2))
      val dv = dt * (-k)* (x + v*dt/2)
      rk2Spring(x + dx, v + dv, t + dt)
    }
  } ensuring (res => res <= 1.0)  // don't diverge

  
  //val dt = 0.05
  //val until = 1.0
  //val k = 1.0 // spring constant

  // this is now parametric in the stepsize dt, until and k are constant parameter 
  def eulerSpringParametric(until: Real, dt: Real, k: Real, x: Real, v: Real, t: Real): Real = {
    require(0 <= x && x <= 1.0 && 0 <= t && t <= 1.0 && 0 <= v && v <= 1.0 && 
      (0.5 * x*x) + (0.5 * v*v) <= 0.5 && 0.0 <= until && until <= 1.0 && 0.00001 <= dt && dt <= 0.1 &&
      0.0 < k && k <= 1.0 )

    if (t >= until) {
      x
    } else {
      eulerSpringParametric(x + v*dt, v + (-k*x*dt), t + dt)
    }
  } ensuring (res => res <= 1.0)  // don't diverge

  def rk2Spring(until: Real, dt: Real, k: Real, x: Real, v: Real, t: Real): Real = {
    require(0 <= x && x <= 1.0 && 0 <= t && t <= 1.0 && 0 <= v && v <= 1.0 && 
      (0.5 * x*x) + (0.5 * v*v) <= 0.5 && 0.0 <= until && until <= 1.0 && 0.00001 <= dt && dt <= 0.1 &&
      0.0 < k && k <= 1.0 )
    
    if (t >= until) {
      x
    } else {
      val dx = dt * (v + (-k*x*dt/2))
      val dv = dt * (-k)* (x + v*dt/2)
      rk2Spring(x + dx, v + dv, t + dt)
    }
  } ensuring (res => res <= 1.0)  // don't diverge

}