
import leon.Real
import Real._


object TaylorSeries {
    
  def cos(x: Real): Real = {
    require(-1.24 <= x && x <= 3.5)
    1 - (x*x)/2.0 + (x*x*x*x)/24.0 - (x*x*x*x*x*x)/720.0
  } ensuring (res => res <= 1.2)

  // sin(x) * cos(x)
  def cos2(x: Real): Real = {// around 1.34
    require(-3.14 <= x && x <= 3.14)
    0.222687 - 0.895344*(x - 1.34) - 0.445375*(x - 1.34)*(x - 1.34) +
    0.596896*(x - 1.34)*(x - 1.34)*(x - 1.34) +
    0.148458*(x - 1.34)*(x - 1.34)*(x - 1.34)*(x - 1.34) -
    0.119379*(x - 1.34)*(x - 1.34)*(x - 1.34)*(x - 1.34)*(x - 1.34) 
  } ensuring (res => res <= 1.2)

  //cos(sqrt(x + 7.8) *2*x)
  def cos3(x: Real): Real = { //around -3.4
    require(-5.0 <= x && x <= -1.0)
    -0.126295 + 2.55374*(x + 3.4) + 0.982769*(x + 3.4)*(x + 3.4) -
    2.67303*(x + 3.4)*(x + 3.4)*(x + 3.4) -
    2.08817*(x + 3.4)*(x + 3.4)*(x + 3.4)*(x + 3.4) +
    0.438815*(x + 3.4)*(x + 3.4)*(x + 3.4)*(x + 3.4)*(x + 3.4)
  } ensuring (res => res <= 1.2)

  def cosh6(x: Real): Real = {
    require(-1.23 <= x && x <= 2.34)
    1 + (x*x)/2.0 + (x*x*x*x)/24.0 + (x*x*x*x*x*x)/720.0
  } ensuring (res => res <= 1.2)

  def exOverCosx(x: Real): Real = {
    require(-1.5 <= x && x <= 0.8)
    1 + x + x*x + (2*x*x*x)/3.0 + (x*x*x*x)/2.0
  } ensuring (res => res <= 5.0)

 
  def sin(x: Real): Real = {
    require(-1.35 <= x && x <= 1.28)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 - (x*x*x*x*x*x*x)/5040.0
  } ensuring (res => res <= 1.2)

  // sin(1.24*x - 0.087)
  def sin2(x: Real): Real = {//around 0.98
    require(-1.0 <= x && x <= 2.46)
    0.903643 + 0.531076*(x - 0.98) - 0.694721*(x - 0.98)*(x - 0.98) -
    0.136097*(x - 0.98)*(x - 0.98)*(x - 0.98) +
    0.0890169*(x - 0.98)*(x - 0.98)*(x - 0.98)*(x - 0.98) +
    0.0104631*(x - 0.98)*(x - 0.98)*(x - 0.98)*(x - 0.98)*(x - 0.98)
  } ensuring (res => res <= 1.2)

  // sin(x) * sin(x)
  def sin3(x: Real): Real = { // around 1.34
    require(-1.0 <= x && x <= 3.14)
    0.947672 + 0.445375*(x - 1.34) - 0.895344*(x - 1.34)*(x - 1.34) -
    0.296916*(x - 1.34)*(x - 1.34)*(x - 1.34) +
    0.298448*(x - 1.34)*(x - 1.34)*(x - 1.34)*(x - 1.34) +
    0.0593833*(x - 1.34)*(x - 1.34)*(x - 1.34)*(x - 1.34)*(x - 1.34) 
  } ensuring (res => res <= 1.2)

  def sinh7(x: Real): Real = {
    require(-0.45 <= x && x <= 2.34)
    x + (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring (res => res <= 1.2)





  def sqrt(x: Real): Real = { // around 3.14
    require(1.35 <= x && x <= 4.28)
    1.772 + 0.282166*(x - 3.14) - 0.0224655*(x - 3.14)*(x - 3.14) +
    0.0035773*(x - 3.14)*(x - 3.14)*(x - 3.14) -
    0.000712043*(x - 3.14)*(x - 3.14)*(x - 3.14)*(x - 3.14) +
    0.000158736*(x - 3.14)*(x - 3.14)*(x - 3.14)*(x - 3.14) 
  } ensuring (res => res <= 1.2)

  // 0.0000272113 is not representable as Int/Int
  /*def sqrt2(x: Real): Real = { // around 7.98
    require(3.35 <= x && x <= 12.28)
    2.82489 + 0.176998*(x- 7.98) - 0.00554505*(x- 7.98)*(x- 7.98) +
    0.000347434*(x- 7.98)*(x- 7.98)*(x- 7.98) -
    0.0000272113*(x- 7.98)*(x- 7.98)*(x- 7.98)*(x- 7.98) 
  } ensuring (res => res <= 1.2)
  */

  // sqrt(3*x - 0.3)
  def sqrt3(x: Real): Real = { // around 3.2
    require(3.35 <= x && x <= 12.28)
    3.04959 + 0.491869*(x - 3.2) - 0.0396669*(x - 3.2)*(x - 3.2) +
    0.00639788*(x - 3.2)*(x - 3.2)*(x - 3.2) -
    0.0012899*(x - 3.2)*(x - 3.2)*(x - 3.2)*(x - 3.2)
  } ensuring (res => res <= 1.2)


  def tan5(x: Real): Real = {
    require(-1.3 <= x && x <= 1.3)
    x + (x*x*x)/3.0 + (2*x*x*x*x*x)/15.0
  } ensuring (res => res <= 3.7)

}
