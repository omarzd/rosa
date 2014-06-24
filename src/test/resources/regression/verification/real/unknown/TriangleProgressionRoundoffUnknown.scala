/* Copyright 2009-2014 EPFL, Lausanne */
import leon.real._
import RealOps._

object TriangleProgressionRoundoffUnknown {

  def triangle1(a: Real, b: Real, c: Real): Real = {
    require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
      a + b > c + 0.1 && a + c > b + 0.1 && b + c > a + 0.1)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  } ensuring (res => 0.29432 < res && res < 35.0741 && res +/- 2.0181e-11)

  def triangle2(a: Real, b: Real, c: Real): Real = {
    require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
      a + b > c + 1e-2 && a + c > b + 1e-2 && b + c > a + 1e-2)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  } ensuring (res => 0.099375 < res && res < 35.0741 && res +/- 6.0243e-11)

  def triangle3(a: Real, b: Real, c: Real): Real = {
    require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
      a + b > c + 1e-3 && a + c > b + 1e-3 && b + c > a + 1e-3)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  } ensuring (res => 3.16031e-2 < res && res < 35.0741 && res +/- 1.8943e-10)

}