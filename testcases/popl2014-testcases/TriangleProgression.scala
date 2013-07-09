import leon.Real
import Real._
import leon.Utils._

object Triangle {

  def triangle1(a: Real, b: Real, c: Real): Real = {
    require(a.in(1.0, 9.0) && b.in(1.0, 9.0) && c.in(1.0, 9.0) &&
      a + b > c + 0.1 && a + c > b + 0.1 && b + c > a + 0.1)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  }

  def triangle01(a: Real, b: Real, c: Real): Real = {
    require(a.in(1.0, 9.0) && b.in(1.0, 9.0) && c.in(1.0, 9.0) &&
      a + b > c + 0.01 && a + c > b + 0.01 && b + c > a + 0.01)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  }

  def triangle001(a: Real, b: Real, c: Real): Real = {
    require(a.in(1.0, 9.0) && b.in(1.0, 9.0) && c.in(1.0, 9.0) &&
      a + b > c + 0.001 && a + c > b + 0.001 && b + c > a + 0.001)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  }


  def triangle0001(a: Real, b: Real, c: Real): Real = {
    require(a.in(1.0, 9.0) && b.in(1.0, 9.0) && c.in(1.0, 9.0) &&
      a + b > c + 0.0001 && a + c > b + 0.0001 && b + c > a + 0.0001)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  }

  def triangle00001(a: Real, b: Real, c: Real): Real = {
    require(a.in(1.0, 9.0) && b.in(1.0, 9.0) && c.in(1.0, 9.0) &&
      a + b > c + 0.00001 && a + c > b + 0.00001 && b + c > a + 0.00001)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  }
}