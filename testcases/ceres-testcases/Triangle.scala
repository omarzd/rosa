
import leon.Real
import Real._


object Triangle {

  // a=9.0, b= SmartFloat(4.8, 0.09), c= SmartFloat(4.8, 0.09)
  def triangleUnstable(a: Real, b: Real, c: Real): Real = {
    require(a.in(1.0, 9.0) && b.in(1.0, 9.0) && c.in(1.0, 9.0) &&
      a + b > c + 0.1 && a + c > b + 0.1 && b + c > a + 0.1)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))

  } ensuring (res => noise(res, 1e-13))


  /*def triangleStable(a: Real, b: Real, c: Real): Real = {
    require(a.in(1.0, 9.0) && b.in(1.0, 9.0) && c.in(1.0, 9.0) &&
      a + b > c + 0.1 && a + c > b + 0.1 && b + c > a + 0.1)

    // for a >= b >= c  c <= b <= a, (a+(b+c)) * (c-(a-b)) * (c+(a-b)) * (a+(b-c))
    if(b < a) {
      if(c < b) {
        //c < b < a
        sqrt((a+(b+c)) * (c-(a-b)) * (c+(a-b)) * (a+(b-c))) / 4.0
      }
      else {
        // b < c < a
        if(c < a) {
          sqrt((a+(c+b)) * (b-(a-c)) * (b+(a-c)) * (a+(c-b))) / 4.0
        }
        else {
          // c -> b, b -> a, a -> c
          // b < a < c
          sqrt((c+(a+b)) * (b-(c-a)) * (b+(c-a)) * (c+(a-b))) / 4.0
        }
      }
    }
    else if(c < b) {
      if (a < c) {
        // a < c < b, a -> b, b -> c, c -> a
        sqrt(b+(c+a)) * (a-(b-c)) * (a+(b-c)) * (b+(c-a)) / 4.0
      } else {
        // c < a < b, a -> b, b -> a, c -> c
        sqrt(b+(a+c)) * (c-(b-a)) * (c+(b-a)) * (b+(a-c)) / 4.0
      }
    } else {
      // a < b < c, a -> c, c -> a
      sqrt(c+(b+a)) * (a-(c-b)) * (a+(c-b)) * (c+(b-a)) / 4.0
    }
  } ensuring (res => noise(res, 1e-13))
  */

  /*def invariant(a: Real, b: Real, c: Real): Boolean = {
    require(a.in(8.4, 8.6) && b.in(4.7, 4.9) && c.in(4.7, 4.9) &&
      a + b > c && a + c > b && b + c > a)

    val t = triangleTextbook(a, b, c)
    val k = triangleKahan(a, b, c)
    ~k <= ~t + 0.001  // 0.001 is the max absolute tolerance
  } holds
  */

}
