import leon.real._
import RealOps._
import annotations._


object Triangles {

  @robust
  def triangle1(a: Real, b: Real, c: Real): Real = {
    require(1.0 < a && a < 9.0 && 1.0 < b &&  b < 9.0 && 1.0 < c && c < 9.0 &&
      a + b > c + 0.1 && a + c > b + 0.1 && b + c > a + 0.1)

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
