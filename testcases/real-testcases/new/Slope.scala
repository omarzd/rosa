import leon.real._
import RealOps._


/*
  Benchmark from "Generating Test Cases inside Suspicious Intervals for Floating-point Number Programs"

  finite difference quotient  f'(x0) = ( f(x0 + h) - f(x0 - h) / 2h )

*/
object Slope {

  // for x*x, for x0 = 13
  def quadratic(h: Real): Real = {
    require(1e-6 <= h && h <= 1e-3)

    ( (13 + h)*(13 + h) - (13 - h)*(13 - h) ) / ( 2*h )

    // the exact derivative is 26
  } ensuring (res => 0 <= res && res <= 25943)  // this is what Fluctuat apparently gives back
  // for doubles there is no problem, but if you run this with floats, you get an error of 66!


}