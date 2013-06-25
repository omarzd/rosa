
import leon.Real
import Real._


object Triangle {

  // a=9.0, b= SmartFloat(4.8, 0.09), c= SmartFloat(4.8, 0.09)
  def triangleTextbook(a: Real, b: Real, c: Real): Real = {
    require(a.in(8.4, 8.6) && b.in(4.7, 4.9) && c.in(4.7, 4.9) && roundoff(a, b, c))

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))

  } ensuring (res => noise(res, 1e-13))


  def triangleKahan(a: Real, b: Real, c: Real): Real = {
    require(a.in(8.4, 8.6) && b.in(4.7, 4.9) && c.in(4.7, 4.9) && roundoff(a, b, c))

    if(b < a) {
      if(c < b) {
        sqrt((c+(b+a)) * (a-(c-b)) * (a+(c-b)) * (c+(b-a))) / 4.0
      }
      else {
        if(c < a) {
          sqrt((b+(c+a)) * (a-(b-c)) * (a+(b-c)) * (b+(c-a))) / 4.0
        }
        else {
          sqrt((b+(a+c)) * (c-(b-a)) * (c+(b-a)) * (b+(a-c))) / 4.0
        }
      }
    }
    else if(c < b) {
      if(b < a) {
        sqrt((c+(a+b)) * (b-(c-a)) * (b+(c-a)) * (c+(a-b))) / 4.0
      }
      else {
        sqrt((a+(c+b)) * (b-(a-c)) * (b+(a-c)) * (a+(c-b))) / 4.0
      }
    } else {
      sqrt((a+(b+c)) * (c-(a-b)) * (c+(a-b)) * (a+(b-c))) / 4.0
    }
  } ensuring (res => noise(res, 1e-13))

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

  
}
