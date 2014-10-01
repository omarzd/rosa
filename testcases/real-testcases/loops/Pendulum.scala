import leon.real._
import RealOps._
import annotations._

object Pendulum {

  def sine(x: Real): Real = {
    require(-20 <= x && x <= 20)

    x - x*x*x/6

  }


  def pendulum(t: Real, w: Real, n: LoopCounter): (Real, Real) = {
    require(-1.5 <= t && t <= 1.5 && -3.5 <= w && w <= 3.5 &&
      //-2.0 <= ~t && ~t <= 2.0 && 5.0 <= ~w && ~w <= 5.0 &&
      4.903325*(t*t - t*t*t*t/12) + w*w/2 <= 4.49)

    if (n < 100) {
      val h: Real = 0.01
      val L: Real = 1.0
      val b: Real = 0.5
      val m: Real = 1.0
      val g: Real = 9.80665


      val k1t = w
      val k1w = -g/L * sine(t) - b/m*w
      val k2t = w + h/2*k1w
      val k2w = -g/L * sine(t + h/2*k1t) - b/m*(w + h/2*k1w)
      val tNew = t + h*k2t
      val wNew = w + h*k2w

      pendulum(tNew, wNew, n++)

    } else {
      (t, w)
    }

  } ensuring (_ match {
    case (tRes, wRes) =>
      -1.0 <= t && t <= 1.0 && -3.2 <= w && w <= 3.2
      // && -2.0 <= ~t && ~t <= 2.0 && 5.0 <= ~w && ~w <= 5.0
    })





  /*def pendulum(t: Real, w: Real, n: LoopCounter): (Real, Real) = {
    require(-2.0 <= t && t <= 2.0 && -5.3 <= w && w <= 5.3 &&
      //-2.0 <= ~t && ~t <= 2.0 && 5.0 <= ~w && ~w <= 5.0 &&
      4.903325*t*t + w*w/2 <= 13.8882)

    if (n < 100) {
      val h: Real = 0.01
      val L: Real = 1.0
      val b: Real = 0.5
      val m: Real = 1.0
      val g: Real = 9.80665


      val k1t = w
      val k1w = -g/L * sine(t) - b/m*w
      val k2t = w + h/2*k1w
      val k2w = -g/L * sine(t + h/2*k1t) - b/m*(w + h/2*k1w)
      val tNew = t + h*k2t
      val wNew = w + h*k2w

      pendulum(tNew, wNew, n++)

    } else {
      (t, w)
    }

  } ensuring (_ match {
    case (tRes, wRes) =>
      -2.0 <= t && t <= 2.0 && 5.0 <= w && w <= 5.0
      // && -2.0 <= ~t && ~t <= 2.0 && 5.0 <= ~w && ~w <= 5.0
    })*/






  /*def smallAngle(th: Real, thP: Real, i: LoopCounter): (Real, Real) = {
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
  })*/

}