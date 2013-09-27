import leon.Real
import Real._

/*
  The idea is that we may not have trigonometric functions available,
  or that full precision is not necessary. In that case, one can use
  an approximation, but we still need to check that it is valid.

  All angles are in radians.
*/
object Sines {


  /*def comparisonValid(x: Real): Real = {
    require(-2.0 < x && x < 2.0)
    val z1 = sineTaylor(x)
    val z2 = sineOrder3(x)
    z1 - z2
  } ensuring(res => ~res <= 0.1)

  def comparisonInvalid(x: Real): Real = {
    require(-2.0 < x && x < 2.0)
    val z1 = sineTaylor(x)
    val z2 = sineOrder3(x)
    z1 - z2
  } ensuring(res => ~res <= 0.01) // counterexample: 1.0
  */

  def sineTaylor(x: Real): Real = {
    require(-2.0 < x && x < 2.0)

    if (x < 0.2) { // small angle approximation
      x
    } else {
      x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 - (x*x*x*x*x*x*x)/5040.0 
    }
  } ensuring(res => -1.0 < res && res < 1.0 && res +/- 1e-14)

  // 3rd order approximation derived with conditions
  // sin(Pi/2) = 1 and sin'(Pi/2)=0
  //http://www.coranac.com/2009/07/sines/
  def sineOrder3(x: Real): Real = {
    require(-2.0 < x && x < 2.0)

    // 3/Pi x - 4/(Pi^3)x^3
    0.954929658551372 * x -  0.12900613773279798*(x*x*x)
  } ensuring(res => -1.0 < res && res < 1.0 && res +/- 1e-14)


  // formula in radians
  def bhaskarasSine(x: Real): Real = {
    (16*x(Pi - x)) / (5*Pi*Pi - 4*x*(Pi - x))
  }

  // Also have a look at: http://lab.polygonal.de/?p=205
}