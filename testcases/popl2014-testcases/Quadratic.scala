
import leon.Real
import Real._
import leon.Utils._

object Quadratic {
  def classicRoot1(a: Real, b: Real, c: Real): Real = {
    require(a.in(1.0, 7.0) && b.in(-10.0, 10.0) && c.in(-5.0, 7.5) &&
      b*b - a * c * 4.0 > 0.1)
    val discr = b*b - a * c * 4.0
    (-b - sqrt(discr))/(a * 2.0)
  } ensuring (res => res +/- 1e-12)

  def classicRoot2(a: Real, b: Real, c: Real): Real = {
    require(a.in(1.0, 7.0) && b.in(-10.0, 10.0) && c.in(-5.0, 7.5) &&
      b*b - a * c * 4.0 > 0.1)
    val discr = b*b - a * c * 4.0
    (-b + sqrt(discr))/(a * 2.0)
  } ensuring (res => res +/- 1e-12)


  def smartRoot1(a: Real, b: Real, c: Real): Real = {
    require(a.in(1.0, 7.0) && b.in(-10.0, 10.0) && c.in(-5.0, 7.5) &&
      b*b - a * c * 4.0 > 0.1)

    val discr = b*b - a * c * 4.0
    if (b*b - a*c > 10 && b > 0) {
      (2.0 * c)/(-b + sqrt(discr))
    } else {
      (-b - sqrt(discr))/(a * 2.0)
    }
  } ensuring (res => res +/- 1e-12)

  def smartRoot2(a: Real, b: Real, c: Real): Real = {
    require(a.in(1.0, 7.0) && b.in(-10.0, 10.0) && c.in(-5.0, 7.5) &&
      b*b - a * c * 4.0 > 0.1)

    val discr = b*b - a * c * 4.0
    if (b*b - a*c > 10 && b > 0) {
      (2.0 * c)/(-b - sqrt(discr))
    } else {
      (-b + sqrt(discr))/(2.0 * a)
    }
  } ensuring (res => res +/- 1e-12)



  /*def invariant1(a: Real, b: Real, c: Real): Boolean = {
    require(a.in(1.0, 7.0) && b.in(20.0, 60.0) && c.in(-5.0, 7.5) &&
      b*b - a * c * 4.0 > 0.1)

    val c1 = classicRoot1General(a, b, c)
    val s1 = smartRoot1General(a, b, c)
    //s1 == c1 + 0.001
    s1 <= c1 + 0.001
  } holds

  def invariant2(a: Real, b: Real, c: Real): Boolean = {
    require(a.in(1.0, 7.0) && b.in(20.0, 60.0) && c.in(-5.0, 7.5) &&
      b*b - a * c * 4.0 > 0.1)

    val c2 = classicRoot2General(a, b, c)
    val s2 = smartRoot2General(a, b, c)
    //s2 == c2 + 0.001
    s2 <= c2 + 0.001
  } holds
  */

}
