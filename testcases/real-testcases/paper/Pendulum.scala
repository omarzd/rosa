import leon.real._
import RealOps._


object Pendulum {

  def sine(x: Real): Real = {
    require(-20 <= x && x <= 20)

    x - x*x*x/6 + x*x*x*x*x/120

  }

  def pendulum(t: Real, w: Real, n: LoopCounter): (Real, Real) = {
    require(-2 <= t && t <= 2 && -5 <= w && w <= 5 &&
      -2.01 <= ~t && ~t <= 2.01 && -5.01 <= ~w && ~w <= 5.01)

    if (n < 3) {
      val h: Real = 0.01
      val L: Real = 2.0
      val m: Real = 1.5
      val g: Real = 9.80665

      val k1t = w
      val k1w = -g/L * sine(t)
      val k2t = w + h/2*k1w
      val k2w = -g/L * sine(t + h/2*k1t)
      val tNew = t + h*k2t
      val wNew = w + h*k2w

      pendulum(tNew, wNew, n++)

    } else {
      (t, w)
    }

  } ensuring (_ match {
    case (tRes, wRes) =>
      -2 <= tRes && tRes <= 2 && -5 <= wRes && wRes <= 5
    })
    


}