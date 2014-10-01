/* Copyright 2009-2014 EPFL, Lausanne */
import leon.real._
import RealOps._

object TriangleProgressionValid {

  def triangle1(a: Real, b: Real, c: Real): Real = {
    require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
      a + b > c + 0.1 && a + c > b + 0.1 && b + c > a + 0.1)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  } ensuring (res => 0.29663 < res && res < 35.0741 && res +/- 2.693e-11)

  def triangle2(a: Real, b: Real, c: Real): Real = {
    require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
      a + b > c + 1e-2 && a + c > b + 1e-2 && b + c > a + 1e-2)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  } ensuring (res => 0.099375 < res && res < 35.0741 && res +/- 8.04e-11)

  def triangle3(a: Real, b: Real, c: Real): Real = {
    require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
      a + b > c + 1e-3 && a + c > b + 1e-3 && b + c > a + 1e-3)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  } ensuring (res => 0.0316 < res && res < 35.0741 && res +/- 2.53e-10)


  /*def triangle4(a: Real, b: Real, c: Real): Real = {
    require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
      a + b > c + 1e-4 && a + c > b + 1e-4 && b + c > a + 1e-4)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  } ensuring (res => 9.9993e-3 < res && res < 35.0741 && res +/- 7.99e-10)

  def triangle5(a: Real, b: Real, c: Real): Real = {
    require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
      a + b > c + 1e-5 && a + c > b + 1e-5 && b + c > a + 1e-5)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  } ensuring (res => 3.1622e-3 < res && res < 35.0741 && res +/- 2.53e-9)

  def triangle6(a: Real, b: Real, c: Real): Real = {
    require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
      a + b > c + 1e-6 && a + c > b + 1e-6 && b + c > a + 1e-6)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  } ensuring (res => 9.9988e-4 < res && res < 35.0741 && res +/- 7.99e-9)

  def triangle7(a: Real, b: Real, c: Real): Real = {
    require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
      a + b > c + 1e-7 && a + c > b + 1e-7 && b + c > a + 1e-7)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  } ensuring (res => 3.1567e-4 < res && res < 35.0741 && res +/- 2.54e-8)

  def triangle8(a: Real, b: Real, c: Real): Real = {
    require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
      a + b > c + 1e-8 && a + c > b + 1e-8 && b + c > a + 1e-8)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  } ensuring (res => 9.8888e-5 < res && res < 35.0741 && res +/- 8.08e-8)

  def triangle9(a: Real, b: Real, c: Real): Real = {
    require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
      a + b > c + 1e-9 && a + c > b + 1e-9 && b + c > a + 1e-9)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  } ensuring (res => 3.0517e-5 < res && res < 35.0741 && res +/- 2.62e-7)
  */

}
