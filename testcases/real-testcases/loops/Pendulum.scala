import leon.real._
import RealOps._
import annotations._

object Pendulum {


  def smallAngle(th: Real, thP: Real, i: LoopCounter): (Real, Real) = {
    require(-0.2 < th && th < 0.2 && -0.63 < thP && thP < 0.63 &&
      -0.2 < ~th && ~th < 0.2 && -0.63 < ~thP && ~thP < 0.63 &&
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

      smallAngle(th_next, thP_next, i++)
    } else {
      (th, thP)
    }
  } ensuring (_ match {
    case (a, b) => -0.2 < a && a < 0.2 && -0.63 < b && b < 0.63
  })

}