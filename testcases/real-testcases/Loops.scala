import leon.Real
import Real._


object Loops {

  // for example a = 10, xn = 1.6
  def cubeRoot(a: Real, xn: Real): Real = {

    for(i <- 1 until 5) {
        xn = xn * ((xn*xn*xn + 2.0*a)/(2.0*xn*xn*xn + a))
    }

  }



}