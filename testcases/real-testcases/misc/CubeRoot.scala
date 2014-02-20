import leon.Real
import Real._


object CubeRoot {

  // for example a = 10, xn = 1.6
  def cubeRoot(i: Int, a: Real, xn: Real): Real = {
    require(0 <= i && i <= 5 && 0 < a && a < 20 && 0 < xn && xn < 20)
    if (i >= 5) xn
    else {
      cubeRoot(i+1, a, xn * ((xn*xn*xn + 2.0*a)/(2.0*xn*xn*xn + a)))
    }
  } ensuring ( res => res*res*res <= a - tol && a + tol <= res*res*res ) // something like, don't diverge?


  // imperative version
  def cubeRoot(a: Real, x0: Real): Real = {
    val xn = x0
    val i = 1
    while(i < 5) {
      xn = xn * ((xn*xn*xn + 2.0*a)/(2.0*xn*xn*xn + a))
      i = i + 1
    }
    xn
  }



}