import leon.real._
import RealOps._
import annotations._

object Pendulum {


  def smallAngle(th: Real, thP: Real, i: Int): (Real, Real) = {
    require(loopCounter(i) && -0.2 < th && th < 0.2 &&
      -0.63 < thP && thP < 0.63 &&
      //0.5*thP*thP + 4.9*th*th < 0.196)
      thP*thP + 9.8*th*th <= 0.3)

    
    if (i < 100) {

      //val m: Real = 1.0
      //val g: Real = 9.8
      //val l: Real = 1.0
      //val c: Real = 0.9
      //val dt: Real = 0.01


      val th_next = th + 0.001 * thP
      //val thP_next = thP + dt * (- (g/l) * th - (c/(m*l*l)) * thP)
      //val thP_next = thP + 0.001 * (- 9.8 * th - 0.5 * thP)
      val thP_next = (9.995* thP - 0.098 * th)/10

      smallAngle(th_next, thP_next, i + 1)
    } else {
      (th, thP)
    }
  } ensuring (_ match {
    case (a, b) => -0.2 < a && a < 0.2 && -0.63 < b && b < 0.63
  })




  //m = 1, k = 2.3 => w = sqrt(2.3)
  /*@loopbound(10)
  def eulerP(theta: Real, omega: Real, i: Int): (Real, Real) = {
    require(loopCounter(i) && -2.0 <= theta && theta <= 2.0 &&
      -2.0 <= omega && omega <= 2.0 && -2.0 <= ~theta && ~theta <= 2.0 &&
      -2.0 <= ~omega && ~omega <= 2.0)// &&
      //theta*theta/2.0 + omega*omega/2.0 <= 0.042)
    
    if (i < 100) {
      val thetaNext = theta + 0.1 * omega 
      val omegaNext = omega + 0.1 * ((theta*theta*theta)/6.0 - theta - 0.1*omega)
      eulerP(thetaNext, omegaNext, i + 1)
    } else {
      (theta, omega)
    }
  } ensuring (_ match {
    case (a, b) => -0.2 <= a && a <= 0.2 && -0.2 <= b && b <= 0.2 &&
      -0.2 <= ~a && ~a <= 0.2 && -0.2 <= ~b && ~b <= 0.2 
  })
*/
}