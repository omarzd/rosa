import leon.real._
import RealOps._

object Triangle {

  def triangleSimplified(a: Real): Real = {
    require(4.500005 <= a && a <= 6.5)

    val b: Real = 4.0
    val c: Real = 8.5

    if (a < b) {
      sqrt((c+(b+a)) * (a-(c-b)) * (a+(c-b)) * (c+(b-a)))/4.0
    } else {
      sqrt((c+(a+b)) * (b-(c-a)) * (b+(c-a)) * (c+(a-b)))/4.0
    }
  } ensuring (res => res >= 0.0 && res +/- 1e-11)
  
}