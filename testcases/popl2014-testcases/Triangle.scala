
import leon.Real
import Real._
import leon.Utils._

object Triangle {

  // a=9.0, b= SmartFloat(4.8, 0.09), c= SmartFloat(4.8, 0.09)
  def triangleUnstable(a: Real, b: Real, c: Real): Real = {
    require(a.in(1.0, 9.0) && b.in(1.0, 9.0) && c.in(1.0, 9.0) &&
      a + b > c + 0.1 && a + c > b + 0.0001 && b + c > a + 0.1)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  } ensuring (res => 0.0 <= ~res && ~res <= 35.1 && res +/- 8e-10)

  def triangleSorted(a: Real, b: Real, c: Real): Real = {
    require(a.in(1.0, 9.0) && b.in(1.0, 9.0) && c.in(1.0, 9.0) &&
      a + b > c + 0.1 && a + c > b + 0.0001 && b + c > a + 0.1 &&
      a < c && b < c)

    val discr =
      if (a < b) {
        (c+(b+a)) * (a-(c-b)) * (a+(c-b)) * (c+(b-a))
      } else {
        (c+(a+b)) * (b-(c-a)) * (b+(c-a)) * (c+(a-b))      
      }
    sqrt(discr) / 4.0
  } ensuring (res => 0.29 <= ~res && ~res <= 35.1 && res +/- 2e-11)

/*
  def triangleStable2(a: Real, b: Real, c: Real): Real = {
    require(a.in(1.0, 9.0) && b.in(1.0, 9.0) && c.in(1.0, 9.0) &&
      a + b > c + 0.1 && a + c > b + 0.1 && b + c > a + 0.1)

    if(b < a) {
      if(c < b) sqrt((a+(b+c)) * (c-(a-b)) * (c+(a-b)) * (a+(b-c))) / 4.0
      else {
        if(c < a) sqrt((a+(c+b)) * (b-(a-c)) * (b+(a-c)) * (a+(c-b))) / 4.0
        else sqrt((c+(a+b)) * (b-(c-a)) * (b+(c-a)) * (c+(a-b))) / 4.0
      }
    }
    else if(c < b) {
      if (a < c) sqrt(b+(c+a)) * (a-(b-c)) * (a+(b-c)) * (b+(c-a)) / 4.0
      else sqrt(b+(a+c)) * (c-(b-a)) * (c+(b-a)) * (b+(a-c)) / 4.0
    } else {
      sqrt(c+(b+a)) * (a-(c-b)) * (a+(c-b)) * (c+(b-a)) / 4.0
    }
  }// ensuring (res => res +/- 1e-10)
*/
  /*def invariant(a: Real, b: Real, c: Real): Boolean = {
    require(a.in(1.0, 9.0) && b.in(1.0, 9.0) && c.in(1.0, 9.0) &&
      a + b > c + 0.1 && a + c > b + 0.1 && b + c > a + 0.1)

    val t = triangleUnstable(a, b, c)
    val k = triangleStable(a, b, c)
    ~k <= ~t + 0.001  // 0.001 is the max absolute tolerance
  } holds
  */

}
