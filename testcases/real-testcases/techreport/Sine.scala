

import leon.Real
import Real._

/*
  Benchmark from http://www.cprover.org/cdfpl/
  "Numeric Bounds Analysis with Conflict-Driven Learning"
*/
object Sine {

  // false
  def sine1(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring(res => ~res <= 0.99 && ~res >= -0.99)

  // false
  def sine2(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring(res => ~res <= 1.0 && ~res >= -1.0)

  // false
  def sine3(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring(res => ~res <= 1.001 && ~res >= -1.001)

  // true
  def sine4(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring(res => ~res <= 1.01 && ~res >= -1.01)

  // true
  def sine5(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring(res => ~res <= 1.1 && ~res >= -1.1)

  // true
  def sine6(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring(res => ~res <= 1.2 && ~res >= -1.2)

  // true
  def sine7(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring(res => ~res <= 1.5 && ~res >= -1.5)

  // true
  def sine8(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring(res => ~res <= 2.0 && ~res >= -2.0)
}
