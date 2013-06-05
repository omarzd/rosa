
import leon.Real
import Real._


object Triangle {

  // TODO: Not purescala!
  def triangleKahan(aa: Real, bb: Real, cc: Real): Real = {
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

  }

  // a=9.0, b= SmartFloat(4.8, 0.09), c= SmartFloat(4.8, 0.09)
  def triangleTextbook(a: Real, b: Real, c: Real): Real = {

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))

  }

}
