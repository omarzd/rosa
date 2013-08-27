import leon.Real
import Real._


object Assertions {

  def assertion(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    val z = x * x
    assert(~z <= 7.0 && z +/- 1e-9)
    val z2 = z * z
    z2
  } ensuring(res => res <= 4 && 0 <= res)

  
}