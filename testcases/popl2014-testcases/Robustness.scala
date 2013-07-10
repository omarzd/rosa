import leon.Real
import Real._

import leon.Utils._

object Robustness {

  def triangleSorted(a: Real, b: Real, c: Real): Real = {
    require(a.in(1.0, 9.0) && 4.0 <= b && b <= 4.0 && 5.0 <= c && c <= 5.0 &&
      a + b > c + 0.1 && a + c > b + 0.0001 && b + c > a + 0.1 &&
      a < c && b < c && a +/- 1e-13)

    val discr =
      if (a < b) {
        (c+(b+a)) * (a-(c-b)) * (a+(c-b)) * (c+(b-a))
      } else {
        (c+(a+b)) * (b-(c-a)) * (b+(c-a)) * (c+(a-b))      
      }
    sqrt(discr) / 4.0
  } ensuring (res => 0.29 <= ~res && ~res <= 35.1 && res +/- 2e-11)
  
  def cav10(x: Real): Real = {
    require(x.in(0, 10))
    if (x*x - x >= 0) x/10
    else x*x + 2
  } ensuring(res => 0 <= res && res <= 3.0 && res +/- 3.0)
  

  def squareRoot1(x: Real): Real = {
    require( x.in(0,10) )
    if (x < 0.01) 1 + 0.5 * x
    else sqrt(1 + x)
  } ensuring( res => res +/- 1e-10) //not valid

  def squareRoot2(x: Real): Real = {
    require( x.in(0,10) && x +/- 1e-10)
    if (x < 1e-5) 1 + 0.5 * x
    else sqrt(1 + x)
  } ensuring( res => res +/- 1e-10) //valid
  

  def poly(x: Real): Real = {
    require(x.in(-5.0, 5.0) && x +/- 1e-10)
    if(x < 1) x*x + 4*x + 3
    else (x+1)*(x+1)*(x+1)
  } ensuring(res => res +/- 1.2e-8) //valid
  
  def poly2(x: Real): Real = {
    require(x.in(-5.0, 5.0) && x +/- 1e-9)
    if(x < 1) x*x + 4*x + 3
    else (x+1)*(x+1)*(x+1)
  } ensuring(res => res +/- 1.2e-8) //valid
  
}
