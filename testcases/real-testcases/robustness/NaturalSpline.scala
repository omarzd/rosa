import leon.real._
import RealOps._
import annotations._


object NaturalSpline {

  // This thing is robust with respect to any input error

  //@robust
  def spline(x: Real): Real = {
    require(0.0 <= x && x <= 3.0 && x +/- 1e-9)

    if (x <= 1) {
    
      2.8 * x - 0.8*x*x*x         // x \in [0,1]
    
    } else if (x <= 2) {
    
       x*x*x - 5.4*x*x + 8.2*x - 1.8   // x \in [1, 2]

       // 0.8*(x-1) + 2.8*(2-x)-0.8(2-x)^3 +0.2(x-1)^3
    } else {

      -0.2*x*x*x + 1.8*x*x - 6.2*x + 7.8    // x \in [2, 3]

    }

  } ensuring (res => res +/- 2.3e-8)

}