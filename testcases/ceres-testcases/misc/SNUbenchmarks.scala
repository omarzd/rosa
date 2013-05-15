
// Benchmarks from here:
// http://www.cprover.org/goto-cc/examples/snu.html
// Original page is not available any more.

// Some of these benchmarks have been used in the Mixed Abstractions paper.
// It is however unclear exactly which assertions they tried to prove,
// they only said they were checking for fp exceptions.

import math._
import leon.NumericUtils._

// For our purpose these need be made functional
object SNUBenchmarks {

  // The root computation of a quadratic equation
  // we'll use the abs library function instead of our own
  def qurt(a0: Double, a1: Double, a2: Double): (Double, Double, Double, Double) = {
    require(a0 != 0.0)

    val d = a1*a1 - 4*a0*a2
    val w1 = 2*a0
    val w2 = sqrt(abs(d))
    if (d > 0.0) {
      val x1real = (-a1 + w2) / w1
      val x1img = 0.0
      val x2real = (-a1 - w2) / w1
      val x2img = 0.0
      (x1real, x1img, x2real, x2img)
    }
    else if(d == 0.0) {
      val x1real = -a1 / w1
      val x1img = 0.0
      val x2real = x1real
      val x2img = 0.0
      (x1real, x1img, x2real, x2img)
    }
    else {
      val w3 = w2 / w1
      val x1real = -a1 / w1
      val x1img = w2
      val x2real = x1real
      val x2img = -w2
      (x1real, x1img, x2real, x2img)
    }
  // TODO: add postcondition or assertions to guard against arithmetic
  // exceptions (division by zero, overflow, underflow, etc.)
  } ensuring(res => absRoundoff(res._1) <= 1e-8)


  // Square root function implemented by Taylor series
  // This is a iterative code, so not really for what we want
  /*def squareRoot(v: Double): Double = {
    var x = v / 10
    var dx = 0.0
    var diff = 0.0
    val minTol = 0.00001

    var flag = false

    if (val == 0) {
      x = 0
    }
    else {
      for (i <- 1 until 20) {
        if (!flag) {
          val dx = (v - (x*x)) / (2.0 * x)
          x = x + dx
          diff = v - (x*x)
          if (abs(diff) <= minTol) flad = true
        } else {
          x = x
        }
      }
    }
    x
  }*/

}
