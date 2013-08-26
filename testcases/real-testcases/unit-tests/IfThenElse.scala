import leon.Real
import Real._


object IfThenElse {

  def f1(x: Real): Real = {
    require(x >< (0, 5) ) //&& x +/- 1e-5)
    if(x <= 0.2) x
    else 2 * x
  } ensuring( res => res <= 10.0 && res +/- 1e-4)

  def f2(x: Real): Real = {
    require(x >< (0, 5)) // && x +/- 1e-5)
    val z = if(x <= 0.2) x*x
    else 2.0 * x
    //z / 3.0
    z
  } ensuring( res => res <= 3.5 && res +/- 1e-4)

  def f3(x: Real): Real = {
    require(x >< (0, 5) && x +/- 1e-5)
    if(x <= 0.2) x*x
    else if(x <= 1.2) 2.0 * x
    else 1.5 * x
  } ensuring( res => res <= 10.0 && res +/- 1e-4)


}