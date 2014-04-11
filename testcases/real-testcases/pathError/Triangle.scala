import leon.real._
import RealOps._

object Triangle {

  /*def triangleKahan(aa: Real, bb: Real, cc: Real): Real = {
    
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
  

  def triangle(a: Real, b: Real, c: Real): Real = {
    require(1 < a && a < 9 && 1 < b && b < 9 && 1 < c && c < 9 &&
      a + b > c + 0.000001 && a + c > b + 0.000001 && b + c > a + 0.000001)

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
      if(c < a) {
        sqrt((c+(a+b)) * (b-(c-a)) * (b+(c-a)) * (c+(a-b))) / 4.0
      }
      else { 
        sqrt((a+(c+b)) * (b-(a-c)) * (b+(a-c)) * (a+(c-b))) / 4.0
      }
    } else {
      sqrt((a+(b+c)) * (c-(a-b)) * (c+(a-b)) * (a+(b-c))) / 4.0  
    }
    
  } ensuring (res => res +/- 1e-11)

}