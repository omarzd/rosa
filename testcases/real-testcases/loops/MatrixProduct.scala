/*
These benchmarks are inspired from the 
FEVS - Functional Equivalence Verification Suite
vsl.cis.udel.edu/fevs
*/



object MatrixProduct {

  // Computes the matrix product of two matrices
  // We will limit this to 3x3 matrices
  // There is also a vectorized version, si jamais
  def matmatSpec(A: Array[Array[Double]], B: Array[Array[Double]]):
    Array[Array[Double]] = {
    // require(matrices are 3 by 3)
    val C = Array[Double].fill(0.0, 0.0)

    for (i <- 0 until 3) {
      for (j <- 0 until 3) {
        C(i)(j) = 0.0
        for (k <- 0 until 3) {
          C(i)(j) = C(i)(j) + A(i)(k) * B(k)(j)
        }
      }
    }
    C
  }
  
}