import leon.real._
import RealOps._


object Pendulum {

  def sine(x: Real): Real = {
    require(-20 <= x && x <= 20)

    x - x*x*x/6 + x*x*x*x*x/120

  }

  def pendulum5(t: Real, w: Real, n: LoopCounter): (Real, Real) = {
    require(-2 <= t && t <= 2 && -5 <= w && w <= 5 &&
      -2.01 <= ~t && ~t <= 2.01 && -5.01 <= ~w && ~w <= 5.01)

    if (n < 5) {
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

      pendulum5(tNew, wNew, n++)

    } else {
      (t, w)
    }

  } ensuring (_ match {
    case (tRes, wRes) =>
      -2 <= tRes && tRes <= 2 && -5 <= wRes && wRes <= 5
    })
    

  def pendulum10(t: Real, w: Real, n: LoopCounter): (Real, Real) = {
    require(-2 <= t && t <= 2 && -5 <= w && w <= 5 &&
      -2.01 <= ~t && ~t <= 2.01 && -5.01 <= ~w && ~w <= 5.01)

    if (n < 10) {
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

      pendulum10(tNew, wNew, n++)

    } else {
      (t, w)
    }

  } ensuring (_ match {
    case (tRes, wRes) =>
      -2 <= tRes && tRes <= 2 && -5 <= wRes && wRes <= 5
    })
  
  def pendulum15(t: Real, w: Real, n: LoopCounter): (Real, Real) = {
    require(-2 <= t && t <= 2 && -5 <= w && w <= 5 &&
      -2.01 <= ~t && ~t <= 2.01 && -5.01 <= ~w && ~w <= 5.01)

    if (n < 15) {
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

      pendulum15(tNew, wNew, n++)

    } else {
      (t, w)
    }

  } ensuring (_ match {
    case (tRes, wRes) =>
      -2 <= tRes && tRes <= 2 && -5 <= wRes && wRes <= 5
    })
  
  def pendulum20(t: Real, w: Real, n: LoopCounter): (Real, Real) = {
    require(-2 <= t && t <= 2 && -5 <= w && w <= 5 &&
      -2.01 <= ~t && ~t <= 2.01 && -5.01 <= ~w && ~w <= 5.01)

    if (n < 20) {
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

      pendulum20(tNew, wNew, n++)

    } else {
      (t, w)
    }

  } ensuring (_ match {
    case (tRes, wRes) =>
      -2 <= tRes && tRes <= 2 && -5 <= wRes && wRes <= 5
    })
  

  def pendulum25(t: Real, w: Real, n: LoopCounter): (Real, Real) = {
    require(-2 <= t && t <= 2 && -5 <= w && w <= 5 &&
      -2.01 <= ~t && ~t <= 2.01 && -5.01 <= ~w && ~w <= 5.01)

    if (n < 25) {
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

      pendulum25(tNew, wNew, n++)

    } else {
      (t, w)
    }

  } ensuring (_ match {
    case (tRes, wRes) =>
      -2 <= tRes && tRes <= 2 && -5 <= wRes && wRes <= 5
    })
  

  def pendulum50(t: Real, w: Real, n: LoopCounter): (Real, Real) = {
    require(-2 <= t && t <= 2 && -5 <= w && w <= 5 &&
      -2.01 <= ~t && ~t <= 2.01 && -5.01 <= ~w && ~w <= 5.01)

    if (n < 50) {
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

      pendulum50(tNew, wNew, n++)

    } else {
      (t, w)
    }

  } ensuring (_ match {
    case (tRes, wRes) =>
      -2 <= tRes && tRes <= 2 && -5 <= wRes && wRes <= 5
    })
  

  def pendulum100(t: Real, w: Real, n: LoopCounter): (Real, Real) = {
    require(-2 <= t && t <= 2 && -5 <= w && w <= 5 &&
      -2.01 <= ~t && ~t <= 2.01 && -5.01 <= ~w && ~w <= 5.01)

    if (n < 100) {
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

      pendulum100(tNew, wNew, n++)

    } else {
      (t, w)
    }

  } ensuring (_ match {
    case (tRes, wRes) =>
      -2 <= tRes && tRes <= 2 && -5 <= wRes && wRes <= 5
    })
  

  def pendulum250(t: Real, w: Real, n: LoopCounter): (Real, Real) = {
    require(-2 <= t && t <= 2 && -5 <= w && w <= 5 &&
      -2.01 <= ~t && ~t <= 2.01 && -5.01 <= ~w && ~w <= 5.01)

    if (n < 250) {
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

      pendulum250(tNew, wNew, n++)

    } else {
      (t, w)
    }

  } ensuring (_ match {
    case (tRes, wRes) =>
      -2 <= tRes && tRes <= 2 && -5 <= wRes && wRes <= 5
    })
  

  def pendulum500(t: Real, w: Real, n: LoopCounter): (Real, Real) = {
    require(-2 <= t && t <= 2 && -5 <= w && w <= 5 &&
      -2.01 <= ~t && ~t <= 2.01 && -5.01 <= ~w && ~w <= 5.01)

    if (n < 500) {
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

      pendulum500(tNew, wNew, n++)

    } else {
      (t, w)
    }

  } ensuring (_ match {
    case (tRes, wRes) =>
      -2 <= tRes && tRes <= 2 && -5 <= wRes && wRes <= 5
    })
  

  def pendulum1000(t: Real, w: Real, n: LoopCounter): (Real, Real) = {
    require(-2 <= t && t <= 2 && -5 <= w && w <= 5 &&
      -2.01 <= ~t && ~t <= 2.01 && -5.01 <= ~w && ~w <= 5.01)

    if (n < 1000) {
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

      pendulum1000(tNew, wNew, n++)

    } else {
      (t, w)
    }

  } ensuring (_ match {
    case (tRes, wRes) =>
      -2 <= tRes && tRes <= 2 && -5 <= wRes && wRes <= 5
    })
  
}