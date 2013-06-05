

import leon.Real
import Real._



object CubeRoot {

  //val a: AffineFloat = 10, var xn = AffineFloat(1.6)
  def cubeRoot(a: Real, xn: Real): Real = {

    for(i <- 1 until 5) {
        xn = xn * ((xn*xn*xn + 2.0*a)/(2.0*xn*xn*xn + a))
    }

  }



}
