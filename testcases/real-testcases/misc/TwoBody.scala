import leon.Real
import Real._

object TwoBody {

  // Fix the masses
  // Let the main mass be fixed at the origin
  def oneBody(x: Real, y: Real, u: Real, v: Real): (Real, Real) = {
    val M: Real = 1
    val m: Real = 0.12 
    val G: Real = 9.81

    if(t < tMax) {
      val dx = x
      val dy = y
      val rSquared = dx*dx + dy*dy
      val r = sqrt(rSquared)

      //assume rSquared is not zero
      val ax = (G * M * m)/(r * rSquared) * dx
      val ay = (G * M * m)/(r * rSquared) * dy

      val newU = u + ax * dt
      val newV = v + ay * dt

      val newX = x + newU * dt
      val newY = y + newV * dt
      
      simulate(newX, newY, newU, newV)
    } else {
      (x, y)
    }

  }


}