/* Copyright 2009-2014 EPFL, Lausanne */
import leon.Real
import Real._

object TriangleProgressionUnknown {

  def triangle1(a: Real, b: Real, c: Real): Real = {
    require(1.0 < a && a < 9.0 && 1.0 < b && b < 9.0 && 1.0 < c && c < 9.0 &&
      a + b > c + 0.1 && a + c > b + 0.1 && b + c > a + 0.1)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  } ensuring (res => 0.29664 < res && res < 35.0741 && res +/- 2.72e-11)

  def triangle1_2(a: Real, b: Real, c: Real): Real = {
    require(1.0 < a && a < 9.0 && 1.0 < b && b < 9.0 && 1.0 < c && c < 9.0 &&
      a + b > c + 0.1 && a + c > b + 0.1 && b + c > a + 0.1)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  } ensuring (res => 0.29432 < res && res < 35.074 && res +/- 2.72e-11)


  def triangle2(a: Real, b: Real, c: Real): Real = {
    require(1.0 < a && a < 9.0 && 1.0 < b && b < 9.0 && 1.0 < c && c < 9.0 &&
      a + b > c + 1e-2 && a + c > b + 1e-2 && b + c > a + 1e-2)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  } ensuring (res => 0.099376 < res && res < 35.0741 && res +/- 8.04e-11)

  def triangle3(a: Real, b: Real, c: Real): Real = {
    require(1.0 < a && a < 9.0 && 1.0 < b && b < 9.0 && 1.0 < c && c < 9.0 &&
      a + b > c + 1e-3 && a + c > b + 1e-3 && b + c > a + 1e-3)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  } ensuring (res => 3.16032e-2 < res && res < 35.0741 && res +/- 2.53e-10)

}
