import leon.Real
import Real._

object NBody {

  @loopbound(10)
  def nBodyRec(x: Real, y: Real, z: Real, vx: Real, vy: Real,
    vz: Real, i: Int): (Real, Real, Real, Real, Real, Real) = {

    require(-6 <= x && x <= 6 && -6 <= y && y <= 6 && -6 <= z && z <= 6 &&
      // check this:
        -6 <= vx && vx <= 6 && -6 <= vy && vy <= 6 && -6 <= vz && vz <= 6 &&
        loopCounter(i))

    if (i < 100) {
      val dt = 0.1
      val solarMass = 39.47841760435743

      val distance = sqrt(x*x + y*y + z*z)
      val mag = dt / (distance * distance * distance)

      val vxNew = vx - x * solarMass * mag
      val vyNew = vy - y * solarMass * mag
      val vzNew = vz - z * solarMass * mag

      val x1 = x + dt * vxNew
      val y1 = y + dt * vyNew
      val z1 = z + dt * vzNew
      nBodyRec(x1, y1, z1, vxNew, vyNew, vzNew)
    } else {
      (x, y, z, vx, vy, vz)
    }
  } ensuring (_ match {
    case (xP, yP, zP, vxP, vyP, vzP) =>
      -6 <= xP && xP <= 6 && -6 <= yP && yP <= 6 && -6 <= zP && zP <= 6 &&
        -6 <= vxP && vxP <= 6 && -6 <= vyP && vyP <= 6 && -6 <= vzP && vzP <= 6
  })




  /*def nBodySimulation(x: Real, y: Real, z: Real, vx: Real, vy: Real,
    vz: Real): (Real, Real, Real, Real, Real, Real) = {

    require(-6 <= x && x <= 6 && -6 <= y && y <= 6 && -6 <= z && z <= 6 &&
      // check this:
        -6 <= vx && vx <= 6 && -6 <= vy && vy <= 6 && -6 <= vz && vz <= 6)

    iterate(x, y, z, vx, vy, vz) {
      val dt = 0.1
      val solarMass = 39.47841760435743

      val distance = sqrt(x*x + y*y + z*z)
      val mag = dt / (distance * distance * distance)

      val vxNew = vx - x * solarMass * mag
      val vyNew = vy - y * solarMass * mag
      val vzNew = vz - z * solarMass * mag

      x <== x + dt * vxNew
      y <== y + dt * vyNew
      z <== z + dt * vzNew
      vx <== vxNew
      vy <== vyNew
      vz <== vzNew
    }
  } ensuring (_ match {
    case (a, b, c, d, e, f) => -10 <= a && a <= 10 && -10 <= b && b <= 10
  })*/

}