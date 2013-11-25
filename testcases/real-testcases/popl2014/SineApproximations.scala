import leon.Real
import Real._

import leon.Utils._

//http://www.coranac.com/2009/07/sines/
object SineApproximations {

  def comparisonValid(x: Real): Real = {
    require(-2.0 < x && x < 2.0)
    val z1 = sineTaylor(x)
    val z2 = sineOrder3(x)
    z1 - z2
  } ensuring(res => res <= 0.1 && res +/- 5e-14)

  def comparisonInvalid(x: Real): Real = {
    require(-2.0 < x && x < 2.0)
    val z1 = sineTaylor(x)
    val z2 = sineOrder3(x)
    z1 - z2
  } ensuring(res => res <= 0.01 && res +/- 5e-14) // counterexample: 1.875
  
  def sineTaylor(x: Real): Real = {
    require(-2.0 < x && x < 2.0)

    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 - (x*x*x*x*x*x*x)/5040.0 
  } ensuring(res => -1.0 < res && res < 1.0 && res +/- 1e-14)

  def sineOrder3(x: Real): Real = {
    require(-2.0 < x && x < 2.0)
    0.954929658551372 * x -  0.12900613773279798*(x*x*x)
  } ensuring(res => -1.0 < res && res < 1.0 && res +/- 1e-14)

}