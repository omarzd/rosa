import leon.real._
import RealOps._


object SmartFloat {

  def triangleTextbook(b: Real, c: Real): Real = {
    require(4.71 <= b && b <= 4.89 && 4.71 <= c && c <= 4.89)
    //require(4.61 <= b && b <= 4.79 && 4.61 <= c && c <= 4.79)
    //require(4.501 <= b && b <= 4.581 && 4.501 <= c && c <= 4.581)

    val a: Real = 9.0
    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))

  }

  def triangle(b: Real, c: Real): Real = {
    require(4.71 <= b && b <= 4.89 && 4.71 <= c && c <= 4.89)
    //require(4.61 <= b && b <= 4.79 && 4.61 <= c && c <= 4.79)
    //require(4.501 <= b && b <= 4.581 && 4.501 <= c && c <= 4.581)

    val a: Real = 9.0

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
    
  }
}
