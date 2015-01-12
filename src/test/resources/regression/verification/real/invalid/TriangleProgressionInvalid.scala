/* Copyright 2009-2015 EPFL, Lausanne */

import RealOps._

object TriangleProgressionInvalid {

  def triangle1(a: Real, b: Real, c: Real): Real = {
    require(1.0 < a && a < 9.0 && 1.0 < b && b < 9.0 && 1.0 < c && c < 9.0 &&
      a + b > c + 0.1 && a + c > b + 0.1 && b + c > a + 0.1)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  } ensuring (res => 0.29432 < res && res < 35.074001 && res +/- 2.72e-11)

}
