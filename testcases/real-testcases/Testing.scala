import leon.real._
import RealOps._
import annotations._

object Testing {

  @model
  def nextItem: Real = { 
    realValue
  } ensuring (res => -1200 <= res && res <= 1200)// && res +/- 1e-8)

  def mean(n: Int, m: Real): Real = {
    // If no actual range is given, take the real one?!
    require(-1200 <= m && m <= 1200 && 2 <= n && n <= 1000 &&
      -1200.5 <= ~m && ~m <= 1200.5)

    if (n < 999) {

      val x = nextItem

      val m_new = ((n - 1.0) * m + x) / n
      mean(n + 1, m_new)
      
    } else {
      m
    }
    
  } ensuring (res => -1200.00 <= res && res <= 1200.00)


  
  /*def test(x: Real, y: Real): Real = {
    require(2 <= x && x <= 3 && 2 <= y && y <= 3 && x +/- 1e-5 && y +/- 1e-6)

    x * y

  }*/

  /*def doppler1(u: Real, v: Real, T: Real): Real = {
    require(-100.0 <= u && u <= 100 && 20 <= v && v <= 20000 && -30 <= T && T <= 50)
    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))
  } ensuring(res => res +/- 1e-12)

  def doppler2(u: Real, v: Real, T: Real): Real = {
    require(-100.0 <= u && u <= 100 && 20 <= v && v <= 20000 && -30 <= T && T <= 50)
    
    (- (331.4 + 0.6 * T) *v) / (((331.4 + 0.6 * T) + u)*((331.4 + 0.6 * T) + u))
  } ensuring(res => res +/- 1e-12)


  def doppler3(u: Real, v: Real, T: Real): Real = {
    require(-100.0 <= u && u <= 100 && 20 <= v && v <= 20000 && -30 <= T && T <= 50 &&
            u +/- 1e-7 && v +/- 1e-9 && T +/- 1e-6)
    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))
  } ensuring(res => res +/- 1e-12)

  def doppler4(u: Real, v: Real, T: Real): Real = {
    require(-100.0 <= u && u <= 100 && 20 <= v && v <= 20000 && -30 <= T && T <= 50 &&
            u +/- 1e-7 && v +/- 1e-9 && T +/- 1e-6)
    (- (331.4 + 0.6 * T) *v) / (((331.4 + 0.6 * T) + u)*((331.4 + 0.6 * T) + u))
  } ensuring(res => res +/- 1e-12)
  */

  /*def jetEngine(x1: Real, x2: Real): Real = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5)

    val t = (3*x1*x1 + 2*x2 - x1)

    x1 + ((2*x1*(t/(x1*x1 + 1))*
    (t/(x1*x1 + 1) - 3) + x1*x1*(4*(t/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(t/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  } ensuring (res => res <= 0)

  def jetEngine2(x1: Real, x2: Real): Real = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5)

    x1 + ((2*x1*(((3*x1*x1 + 2*x2 - x1))/(x1*x1 + 1))*
    (((3*x1*x1 + 2*x2 - x1))/(x1*x1 + 1) - 3) + x1*x1*(4*(((3*x1*x1 + 2*x2 - x1))/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(((3*x1*x1 + 2*x2 - x1))/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  } ensuring (res => res <= 0)
  */
}