import leon.Real
import Real._


object Z3Only {

  def bspline3(u: Real): Real = {
    require(0 <= u && u <= 1 && u +/- 1e-13)
    -u*u*u / 6.0
  } ensuring (res => -0.17 <= res && res <= 0.05 && res +/- 1e-11)
  
}
