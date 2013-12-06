/*
These benchmarks are inspired from the 
FEVS - Functional Equivalence Verification Suite
vsl.cis.udel.edu/fevs
*/

/* diffusion1d_seq.c: sequential version of 1d diffusion.
 * The length of the rod is 1. The endpoints are frozen at the input 
 * temperature.
 *
 */

object Diffusion {
  
  var k = 0.3 // thermal conductivity apparently
  
  /* updates u for next time step. */
  def update(u: List[Double]): List[Double] = {
    require(0 <= u && u <= 100)  // should mean for all elements in u  
    
    for(
      (elem, i) <- u.zipWithIndex
      uBefore <- u(i - 1)
      uAfter <- u(i + 1)
      ) yield elem + k * (uAfter + uBefore - 2 * elem)
  
  // this may fail, because of roundoff errors
  } ensuring ( ??? res => 0 <= u && u <= 100)  


  def main = {
    var points = List(100.0, 0.0, 0.0, 0.0, 100.0)

    for (i <- 0 until numSteps)
      points = update(points)

  }
}