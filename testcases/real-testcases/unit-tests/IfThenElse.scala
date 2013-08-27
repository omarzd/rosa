import leon.Real
import Real._


object IfThenElse {

  def f1(x: Real): Real = {
    require(x >< (0, 5) && x +/- 1e-5)
    if(x <= 0.2) x
    else 2 * x
  } ensuring(res => res <= 10.0 && res +/- 1e-4)


  def f2(x: Real): Real = {
    require(x >< (0, 5) && x +/- 1e-5)
    val z = if(x <= 0.2) x
    else 2.0 * x
    z / 3.0
  } ensuring( res => res <= 3.5 && res +/- 1e-4)

  def f3(x: Real): Real = {
    require(x >< (0, 5) && x +/- 1e-5)

    if(x <= 0.2) x
    else if(x <= 1.2) 2.0 * x
    else 1.5 * x
  } ensuring( res => res <= 10.0 && res +/- 1e-4)


  def f4(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    if(x * x <= 0) {
      if(y <= 5.4) {
        x * x + y
      } else {
        x / y
      }
    } else {
      x / y
    }
  } ensuring(res => ~res <= 4 && 0 <= ~res)

  def f5(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    val z = if(x * x <= 0) {
      if(y <= 5.4) {
        x * x + y
      } else {
        x / y
      }
    } else {
      x / y
    }
    z * z
  } ensuring(res => res +/- 1e-6)

  /*def f6(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    val z = if(y <= 5.4) {
      val w = x * x + y
      if (x <= 0.5)
        -w
      else 2 * w
    } else {
      val w = x / y
      w * w
    }
    z * z
  } ensuring(res => res +/- 1e-6)  */
}