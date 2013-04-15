
import leon.NumericUtils._


object Debug {

  def bspline1(u: Double): Double = {
    require(0 <= u && u <= 1)
    (3 * u*u*u - 6 * u*u + 4) * (1/6.0)
  } ensuring (res => res >= 0.15 && absRoundoff(res) <= 1e-10)

  /*def beales(x: Double, y: Double): Double = {
    require(-4 <= x && x <= 0.5 && 1.5 <= y && y <= 4.45)
    (1.5 - x + x*y)*(1.5 - x + x*y) +
    (2.25 - x + x*y*(x*y))*(2.25 - x + x*y*(x*y)) +
    (2.625 - x + x*y*(x*y)*(x*y))*(2.625 - x + x*y*(x*y)*(x*y))
  } ensuring (res => res >= -56020.0)*/
  
 
  /*def motzkin(x: Double, y: Double, z: Double): Double = {
    require(-5.6 <= x && x <= 1.3 && 45.3 <= y && y <= 63.0 &&
            3.2 <= z && z <= 15.7)
    z*z*z + x*x*(y*y) * (z*z + y*y - 3*z*z)
  } ensuring (res => res >= -56020.0)
  */

}
