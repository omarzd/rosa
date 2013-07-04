


import leon.Real
import Real._

import leon.Utils._

object Debug {

  def triangle(a: Real, b: Real, c: Real): Real = {
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
  } 
}
