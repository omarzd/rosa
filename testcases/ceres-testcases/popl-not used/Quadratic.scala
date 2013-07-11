
import leon.Real
import Real._
import leon.Utils._

object Quadratic {

  def classicRoot1(a: Real, b: Real, c: Real): Real = {
    require(3 <= a && a <= 3 && 3.5 <= b && b <= 3.5 && c.in(-2, 2) &&
      b*b - a * c * 4.0 > 0.1)

    val discr = b*b - a * c * 4.0
    (-b - sqrt(discr))/(a * 2.0)
  } ensuring (res => res +/- 1e-12)

  def classicRoot2(a: Real, b: Real, c: Real): Real = {
    require(3 <= a && a <= 3 && 3.5 <= b && b <= 3.5 && c.in(-2, 2) &&
      b*b - a * c * 4.0 > 0.1)

    val discr = b*b - a * c * 4.0
    (-b + sqrt(discr))/(a * 2.0)
  } ensuring (res => res +/- 1e-12)

  def smartRoot1(a: Real, b: Real, c: Real): Real = {
    require(3 <= a && a <= 3 && 3.5 <= b && b <= 3.5 && c.in(-2, 2) &&
      b*b - a * c * 4.0 > 0.1)

    val discr = b*b - a * c * 4.0
    if(b*b - a*c > 10.0) {
      if(b > 0.0) (-b - sqrt(discr))/(a * 2.0)
      else if(b < 0.0)  c * 2.0 /(-b + sqrt(discr))
      else  (-b - sqrt(discr))/(a * 2.0)
    }
    else {
      (-b - sqrt(discr))/(a * 2.0)
    }

  } ensuring (res => res +/- 1e-13)

  def smartRoot2(a: Real, b: Real, c: Real): Real = {
    require(3 <= a && a <= 3 && 3.5 <= b && b <= 3.5 && c.in(-2, 2) &&
      b*b - a * c * 4.0 > 0.1)

    val discr = b*b - a * c * 4.0
    if(b*b - a*c > 10.0) {
      if(b > 0.0) c * 2.0 /(-b - sqrt(discr))
      else if(b < 0.0)  (-b + sqrt(discr))/(a * 2.0)
      else (-b + sqrt(discr))/(a * 2.0)
    }
    else {
      (-b + sqrt(discr))/(a * 2.0)
    }
  } ensuring (res => res +/- 3e-15)



/*
  def classicRoot1(a: Real, b: Real, c: Real): Real = {
    require(a.in(2.5, 3.5) && b.in(54.0, 57.0) && c.in(0.5, 1.5) &&

      b*b - a * c * 4.0 > 0.1)
    val discr = b*b - a * c * 4.0
    (-b - sqrt(discr))/(a * 2.0)
  } ensuring (res => res +/- 1e-12)

  def classicRoot2(a: Real, b: Real, c: Real): Real = {
    require(a.in(2.5, 3.5) && b.in(54.0, 57.0) && c.in(0.5, 1.5) &&

      b*b - a * c * 4.0 > 0.1)
    val discr = b*b - a * c * 4.0
    (-b + sqrt(discr))/(a * 2.0)
  } ensuring (res => res +/- 1e-12)


  def smartRoot1(a: Real, b: Real, c: Real): Real = {
    require(a.in(2.5, 3.5) && b.in(54.0, 57.0) && c.in(0.5, 1.5) &&
      b*b - a * c * 4.0 > 0.1)

    val discr = b*b - a * c * 4.0
    if(b*b - a*c > 10.0) {
      if(b > 0.0) (-b - sqrt(discr))/(a * 2.0)
      else if(b < 0.0)  c * 2.0 /(-b + sqrt(discr))
      else  (-b - sqrt(discr))/(a * 2.0)
    }
    else {
      (-b - sqrt(discr))/(a * 2.0)
    }

  } ensuring (res => res +/- 1e-13)
  

  def smartRoot2(a: Real, b: Real, c: Real): Real = {
    require(a.in(2.5, 3.5) && b.in(54.0, 57.0) && c.in(0.5, 1.5) &&
      b*b - a * c * 4.0 > 0.1)

    val discr = b*b - a * c * 4.0
    if(b*b - a*c > 10.0) {
      if(b > 0.0) c * 2.0 /(-b - sqrt(discr))
      else if(b < 0.0)  (-b + sqrt(discr))/(a * 2.0)
      else (-b + sqrt(discr))/(a * 2.0)
    }
    else {
      (-b + sqrt(discr))/(a * 2.0)
    }
  } ensuring (res => res +/- 1e-13)
*/
  

}
