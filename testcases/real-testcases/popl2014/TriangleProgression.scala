import leon.real._
import RealOps._

object TriangleProgression {

  def triangle(a: Real, b: Real, c: Real): Real = {
    require(9.0 <= a && a <= 9.0 && 4.71 <= b && b <= 4.89 && 4.71 <= c && c <= 4.89)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  }// ensuring(res => 6.25 <= res && res <= 8.62 && res +/- 6.9e-14)

  def triangle1(a: Real, b: Real, c: Real): Real = {
    require(1.0 < a && a < 9.0 && 1.0 < b &&  b < 9.0 && 1.0 < c && c < 9.0 &&
      a + b > c + 0.1 && a + c > b + 0.1 && b + c > a + 0.1)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  } ensuring(res => 0.29 <= res && res <= 35.1 && res +/- 2.7e-11  &&
                    0.29 <= ~res && ~res <= 35.1)


  def triangle2(a: Real, b: Real, c: Real): Real = {
    require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
      a + b > c + 1e-2 && a + c > b + 1e-2 && b + c > a + 1e-2)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  }

  def triangle3(a: Real, b: Real, c: Real): Real = {
    require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
      a + b > c + 1e-3 && a + c > b + 1e-3 && b + c > a + 1e-3)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  }


  def triangle4(a: Real, b: Real, c: Real): Real = {
    require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
      a + b > c + 1e-4 && a + c > b + 1e-4 && b + c > a + 1e-4)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  }

  def triangle5(a: Real, b: Real, c: Real): Real = {
    require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
      a + b > c + 1e-5 && a + c > b + 1e-5 && b + c > a + 1e-5)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  }

  def triangle6(a: Real, b: Real, c: Real): Real = {
    require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
      a + b > c + 1e-6 && a + c > b + 1e-6 && b + c > a + 1e-6)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  }

  def triangle7(a: Real, b: Real, c: Real): Real = {
    require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
      a + b > c + 1e-7 && a + c > b + 1e-7 && b + c > a + 1e-7)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  }

  def triangle8(a: Real, b: Real, c: Real): Real = {
    require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
      a + b > c + 1e-8 && a + c > b + 1e-8 && b + c > a + 1e-8)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  }

  def triangle9(a: Real, b: Real, c: Real): Real = {
    require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
      a + b > c + 1e-9 && a + c > b + 1e-9 && b + c > a + 1e-9)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  }

  def triangle10(a: Real, b: Real, c: Real): Real = {
    require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
      a + b > c + 1e-10 && a + c > b + 1e-10 && b + c > a + 1e-10)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  }

  def triangle11(a: Real, b: Real, c: Real): Real = {
    require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
      a + b > c + 1e-11 && a + c > b + 1e-11 && b + c > a + 1e-11)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  }

  def triangle12(a: Real, b: Real, c: Real): Real = {
    require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
      a + b > c + 1e-12 && a + c > b + 1e-12 && b + c > a + 1e-12)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  }
}
