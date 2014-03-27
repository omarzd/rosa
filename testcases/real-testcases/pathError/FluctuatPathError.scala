

//Robustness Analysis of Finite Precision Implementations, arxiv extended version,
// E. Goubault, S. Putot
/*
The analysis finds that the interpolated res is within [-2.25e-5,33.25],
 with an error within [-3.55e-5,2.4e-5], that is of the order of magnitude
 of the input error despite unstable tests.
*/
  def simpleInterpolator(E: Real) {
    require(0.0 <= E && E <= 100.0 && E +/- 0.00001)

    val r1_1: Real = 0.0
    val r1_2: Real = 5 * 2.25
    val r1_3: Real = r1_2 + 20 * 1.1

    if (E < 5)
      E * 2.25 + r1_1
    else if (E < 25)
      (E - 5) * 1.1 + r1_2
    else
      r1_3
  }

/*
Result is in the real number semantics within [1,1.4531]
with a global error within [-0.03941,0.03895],
the discontinuity at the test accounting for most of it, i.e. an error within [-0.03898,0.03898]
*/
def squareRoot(I: Real): Real = {
  // the error should be [0, 0.001]
  require(1.0 <= I && I <= 2.0 && I +/- 0.001)

  val sqrt2: Real = 1.414213538169860839843750

  if (I >= 2)
    sqrt2 * (1.0 + (I/2 - 1) * (0.5 - 0.125 * ( I/2 - 1)))
  else
    1 + (I - 1) * (0.5 + (I-1) * (-0.125 + (I - 1) * 0.0625))
}


