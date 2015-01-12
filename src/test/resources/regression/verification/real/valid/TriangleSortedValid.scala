/* Copyright 2009-2015 EPFL, Lausanne */

import RealOps._
import annotations._

object TriangleSortedValid {

  def mainFunctionStable(a: Real): Real = {
    require(4.500005 <= a && a <= 6.5)

    val b = 4.0
    val c = 8.5
    val area = triangleSorted(a, b, c)
    area
  } ensuring(res => res +/- 1e-11)

  @robust
  def triangleSorted(a: Real, b: Real, c: Real): Real = {
    require(1 < a && a < 9 && 1 < b && b < 9 && 1 < c && c < 9 &&
      a + b > c + 0.000001 && a + c > b + 0.000001 && b + c > a + 0.000001 &&
      a < c && b < c)

    if (a < b) {
      sqrt((c+(b+a)) * (a-(c-b)) * (a+(c-b)) * (c+(b-a)))/4.0
    } else {
      sqrt((c+(a+b)) * (b-(c-a)) * (b+(c-a)) * (c+(a-b)))/4.0
    }
  }
}
