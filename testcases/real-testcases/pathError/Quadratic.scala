import leon.real._
import RealOps._

object Quadratic {

  def smartRootSimple(a: Real, b: Real, c: Real): Real = {
    require(3 <= a && a <= 3 && 3.5 <= b && b <= 3.5 && -2 < c && c < 2 &&
      b*b - a * c * 4.0 > 0.1)

    val discr = b*b - a * c * 4.0
    if(b*b - a*c > 10.0) {
      if(b > 0.0)
        c * 2.0 /(-b - sqrt(discr))
      else if(b < 0.0)  
        (-b + sqrt(discr))/(a * 2.0)
      else
        (-b + sqrt(discr))/(a * 2.0)
    }
    else {
      (-b + sqrt(discr))/(a * 2.0)
    }
  } ensuring (res => res +/- 6e-15)

  def smartRoot(a: Real, b: Real, c: Real): Real = {
    require(2 <= a && a <= 3 && 3.5 <= b && b <= 5.5 && -2 < c && c < 2 &&
      b*b - a * c * 4.0 > 0.1)

    val discr = b*b - a * c * 4.0
    if(b*b - a*c > 10.0) {
      if(b > 0.0)
        c * 2.0 /(-b - sqrt(discr))
      else if(b < 0.0)  
        (-b + sqrt(discr))/(a * 2.0)
      else
        (-b + sqrt(discr))/(a * 2.0)
    }
    else {
      (-b + sqrt(discr))/(a * 2.0)
    }
  } ensuring (res => res +/- 6e-15)

}