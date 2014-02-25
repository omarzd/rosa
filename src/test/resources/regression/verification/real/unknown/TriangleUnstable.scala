/* Copyright 2009-2014 EPFL, Lausanne */
import leon.Real
import Real._


object TriangleUnstable {

  def mainFunctionUnstable(a: Real): Real = {
    require(4.500005 <= a && a <= 6.5)

    val b = 4.0
    val c = 8.5
    val area = triangleUnstable(a, b, c)
    area
  } ensuring(res => res +/- 1e-11)


  def triangleUnstable(a: Real, b: Real, c: Real): Real = {
    require(1 < a && a < 9 && 1 < b && b < 9 && 1 < c && c < 9 &&
      a + b > c + 0.000001 && a + c > b + 0.000001 && b + c > a + 0.000001)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  } 
}