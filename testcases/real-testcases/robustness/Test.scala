import leon.real._
import RealOps._

object Test {


  /*def squareRoot3(x: Real): Real = {
    require(0 < x && x < 10 && x +/- 1e-10 )
    if (x < 1e-5) 1 + 0.5 * x
    else sqrt(1 + x)
  } ensuring( res => res +/- 1e-10) //valid


  def interpolator(e: Real): Real = {
    require(0.0 <= e && e <= 100.0 && e +/- 0.00001)

    if (e < 5.0) {
      e * 2.25
    } else if (e < 25.0) {
      (e - 5.0) * 1.1 + 11.25
    } else {
      val r: Real = 33.25
      r
    }

  } ensuring( res => res >= 0 && res +/- 0.02)
  */
  def triangleSorted(a: Real, b: Real, c: Real): Real = {
    require(1 < a && a < 9 && 1 < b && b < 9 && 1 < c && c < 9 &&
      a + b > c + 0.000001 && a + c > b + 0.000001 && b + c > a + 0.000001 &&
      a < c && b < c)

    if (a < b) {
      sqrt((c+(b+a)) * (a-(c-b)) * (a+(c-b)) * (c+(b-a)))/4.0
    } else {
      sqrt((c+(a+b)) * (b-(c-a)) * (b+(c-a)) * (c+(a-b)))/4.0
    }
  } ensuring( res => res +/- 1e-11)
  
}