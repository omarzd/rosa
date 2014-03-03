import leon.Real
import Real._

object NBody {

  def nBodySimulation(x: Real, y: Real, z: Real, vx: Real, vy: Real,
    vz: Real): (Real, Real, Real, Real, Real, Real) = {

    require(-6 <= x && x <= 6 && -6 <= y && y <= 6 && -6 <= z && z <= 6 &&
      // check this:
        -6 <= vx && vx <= 6 && -6 <= vy && vy <= 6 && -6 <= vz && vz <= 6)

    iterate {
      val dt = 0.1
      val solarMass = 39.47841760435743

      val distance = math.sqrt(x*x + y*y + z*z)
      val mag = dt / (distance * distance * distance)

      val vxNew = vx - x * solarMass * mag
      val vyNew = vy - y * solarMass * mag
      val vzNew = vz - z * solarMass * mag

      x <= x + dt * vxNew
      y <= y + dt * vyNew
      z <= z + dt * vzNew
      vx <= vxNew
      vy <= vyNew
      vz <= vzNew
    }
  }

}