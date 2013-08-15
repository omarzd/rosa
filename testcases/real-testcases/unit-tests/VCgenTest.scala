import leon.Real
import Real._


object VCgenTest {

  def arithmetic(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    x * (sqrt(x) - y) / x + (-x)
  } ensuring (res => res <= 0 && res +/- 1e-6)

  def ifThenElse(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    if(x * x <= 0 && y <= 5.4) {
      x * x + y
    } else {
      x / y
    }
  } ensuring(res => ~res <= 4 && 0 <= ~res)

  def ifThenElse2(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    val z = if(x * x <= 0 && y <= 5.4) {
      x * x + y
    } else {
      x / y
    }
    z * z
  }

  def ifThenElse3(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    val z = if(x * x <= 0 && y <= 5.4) {
      val w = x * x + y
      if (x <= 0.5)
        -w
      else 2 * w
    } else {
      x / y
    }
    z * z
  }  

  
  def assertion(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    val z = x * x
    assert(~z <= 7.0 && z +/- 1e-9)
    val z2 = z * z
    z2
  } ensuring(res => res <= 4 && 0 <= res)

  

  def functionCall(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    arithmetic(x * x, y * y)
  }
  
}