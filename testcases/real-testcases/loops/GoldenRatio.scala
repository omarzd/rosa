/*
These benchmarks are inspired from the 
FEVS - Functional Equivalence Verification Suite
vsl.cis.udel.edu/fevs
*/

object GoldenRation {


  // Computes an approximation of the golden ratio using Fibonacci numbers
  def fibSpec(tol: Double) = {
    require(tol > 0.0)
    var i = 1.0
    var j = 1.0
    var err = 0.0
    var tmp = 0.0
    var p = 0.0
    err = tol

    while(err >= tol) {
      i = j
      j = k
      k = i + j
      tmp = k / j
      if (tmp >= p)
        err = tmp - p
      else
        err = p - tmp
      p = tmp
    }
    p
  } ensuring (res => res <= (1 + sqrt(5))/2.0 + tol)

  // Computes an approximation of the golden ratio using Fibonacci numbers
  def fibImpl(tol: Double) = {
    require(tol > 0.0)
    var j = 1.0
    var k = 1.0
    var err = 0.0
    var p = 0.0
    err = tol

    while(err >= tol) {
      k = j + k
      j = k - j
      err = k/j - p
      p = err + p
      if (err < 0) err = -err
    }
    p
  } ensuring (res => res <= (1 + sqrt(5))/2.0 + tol)
}
