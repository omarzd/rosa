
import leon.Real
import Real._
import leon.Utils._

object Triangle {

  // a=9.0, b= SmartFloat(4.8, 0.09), c= SmartFloat(4.8, 0.09)
  def triangleUnstable(a: Real, b: Real, c: Real): Real = {
    require(a.in(1.0, 9.0) && b.in(1.0, 9.0) && c.in(1.0, 9.0) &&
      a + b > c + 0.1 && a + c > b + 0.1 && b + c > a + 0.1)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  } ensuring (res => noise(res, 1e-13))


  def triangleStable(a: Real, b: Real, c: Real): Real = {
    require(a.in(1.0, 9.0) && b.in(1.0, 9.0) && c.in(1.0, 9.0) &&
      a + b > c + 0.1 && a + c > b + 0.1 && b + c > a + 0.1)

    // for a >= b >= c  c <= b <= a, (a+(b+c)) * (c-(a-b)) * (c+(a-b)) * (a+(b-c))
    if(b < a) {
      if(c < b) sqrt((a+(b+c)) * (c-(a-b)) * (c+(a-b)) * (a+(b-c))) / 4.0 //c < b < a
      else {
        if(c < a) sqrt((a+(c+b)) * (b-(a-c)) * (b+(a-c)) * (a+(c-b))) / 4.0 // b < c < a
        else sqrt((c+(a+b)) * (b-(c-a)) * (b+(c-a)) * (c+(a-b))) / 4.0  // b < a < c
      }
    }
    else if(c < b) {
      if (a < c) sqrt(b+(c+a)) * (a-(b-c)) * (a+(b-c)) * (b+(c-a)) / 4.0  // a < c < b
      else sqrt(b+(a+c)) * (c-(b-a)) * (c+(b-a)) * (b+(a-c)) / 4.0  // c < a < b
    } else {
      sqrt(c+(b+a)) * (a-(c-b)) * (a+(c-b)) * (c+(b-a)) / 4.0  // a < b < c
    }
  } ensuring (res => noise(res, 1e-13))

  def invariant(a: Real, b: Real, c: Real): Boolean = {
    require(a.in(1.0, 9.0) && b.in(1.0, 9.0) && c.in(1.0, 9.0) &&
      a + b > c + 0.1 && a + c > b + 0.1 && b + c > a + 0.1)

    val t = triangleUnstable(a, b, c)
    val k = triangleStable(a, b, c)
    ~k <= ~t + 0.001  // 0.001 is the max absolute tolerance
  } holds


}
