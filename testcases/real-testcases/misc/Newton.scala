import leon.Real
import Real._


object NewtonsMethod {

  // In CDFPL benchmarks, the input variable was the starting value,
  // the number of iterations was fixed (to 3).

  // Test function from CDFPL benchmark:
  //def f(x: Real): Real = {
  //  x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  //}

  //def fp(x: Real): Real = {
  //  1 - (x*x)/2.0 + (x*x*x*x)/24.0 + (x*x*x*x*x*x)/720.0
  //}

  def computeRoot(start: Double, tol: Double): Double = {

    var err = 2 * tol
    var xn = start
    var count = 0
    while(err > tol && count < 100) {
      xn = xn - f(xn)/fprime(xn)
      err = math.abs(f(xn))
      count += 1
    }

    if (count == 100) { println("Diverged!"); return Double.NaN }
    return xn
  }

}