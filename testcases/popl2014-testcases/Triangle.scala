
import leon.Real
import Real._
import leon.Utils._

object Triangle {

  def triangleUnstable(a: Real, b: Real, c: Real): Real = {
    require(a.in(1.0, 9.0) && b.in(1.0, 9.0) && c.in(1.0, 9.0) && a +/- 1e-10 &&
      a + b > c + 0.1 && a + c > b + 0.0001 && b + c > a + 0.1)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  } ensuring (res => 0.0 <= ~res && ~res <= 35.1 && res +/- 8e-10)

  def triangleSorted(a: Real, b: Real, c: Real): Real = {
    require(a.in(1.0, 9.0) && b.in(1.0, 9.0) && c.in(1.0, 9.0) && a +/- 1e-10 &&
      a + b > c + 0.1 && a + c > b + 0.0001 && b + c > a + 0.1 &&
      a < c && b < c)

    val discr =
      if (a < b) {
        (c+(b+a)) * (a-(c-b)) * (a+(c-b)) * (c+(b-a))
      } else {
        (c+(a+b)) * (b-(c-a)) * (b+(c-a)) * (c+(a-b))      
      }
    sqrt(discr) / 4.0
  } ensuring (res => 0.29 <= ~res && ~res <= 35.1 && res +/- 2e-11)
}
