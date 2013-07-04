


import leon.Real
import Real._

import leon.Utils._

object Debug {

  def smartRoot1General(a: Real, b: Real, c: Real): Real = {
    require(a.in(1.0, 7.0) && b.in(20.0, 60.0) && c.in(-5.0, 7.5) &&
      b*b - a * c * 4.0 > 0.1)

    val discr = b*b - a * c * 4.0
    if(b*b - a*c > 10.0) {
      if(b > 0.0) (-b - sqrt(discr))/(a * 2.0)
      else if(b < 0.0)  c * 2.0 /(-b + sqrt(discr))
      else  (-b - sqrt(discr))/(a * 2.0)
    }
    else {
      (-b - sqrt(discr))/(a * 2.0)
    }

  } ensuring (res => noise(res, 1e-10))

}
