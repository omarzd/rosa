
import leon.Real
import Real._


object Triangle {

  // TODO: Not purescala!
  /*def triangleKahan(aa: Real, bb: Real, cc: Real): Real = {
    require(aa in ())
    var a = aa
    var b = bb
    var c = cc

    if(b < a) {
      val t = a
      if(c < b) {
        a = c; c = t
      }
      else {
        if(c < a) {
          a = b; b = c; c = t
        }
        else {
          a = b; b = t
        }
      }
    }
    else if(c < b) {
      val t = c; c = b;
      if(c < a) {
        b = a; a = t
      }
      else {
        b = t
      }
    }
    sqrt((a+(b+c)) * (c-(a-b)) * (c+(a-b)) * (a+(b-c))) / 4.0

  }*/

  // a=9.0, b= SmartFloat(4.8, 0.09), c= SmartFloat(4.8, 0.09)
  def triangleTextbook(a: Real, b: Real, c: Real): Real = {
    require(a.in(9.2, 9.5) && b.in(4.7, 4.9) && c.in(4.7, 4.9) && roundoff(a, b, c))

    //val s = (a + b + c)/2.0
    //sqrt(s * (s - a) * (s - b) * (s - c))
    sqrt(a)
  } ensuring (res => noise(res, 1e-13))

}
