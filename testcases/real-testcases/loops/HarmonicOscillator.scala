import leon.real._
import RealOps._
import annotations._

object HarmonicOscillator {

  // TODO: to make this inductive, include some energy loss term

  /**
    Potential energy: E = 0.5 ( m v^2 + k x^2)
    here: m = 1, k = 2.3, E_initial = 115 (for v=0, x=10)
  */
  @loopbound(10)
  def eulerRec(x: Real, v: Real, i: Int): (Real, Real) = {
    require(loopCounter(i) && -10.0 <= x && x <= 10.0 && -10.0 <= v && v <= 10.0 &&
      0.5*(v*v + 2.3*x*x) <= 115)
    
    if (i < 100) {
      eulerRec(x + 0.1 * v, v - 2.3 * 0.1 * x, i + 1)
    } else {
      (x, v)
    }
  } ensuring (_ match {
    case (a, b) => -10 <= a && a <= 10 && -10 <= b && b <= 10   
  })

  @loopbound(10)
  def rk2Rec(x: Real, v: Real, i: Int): (Real, Real) = {
    require(loopCounter(i) && -10.0 <= x && x <= 10.0 && -10.0 <= v && v <= 10.0 &&
       0.5*(v*v + 2.3*x*x) <= 115)

    if (i < 100) {
      val k: Real = 2.3
      val h: Real = 0.1
      
      val dx = h * (v + (-k*x*h/2))
      val dv = h * (-k)* (x + v*h/2)

      rk2Rec(x + dx, v + dv, i + 1)
    } else {
      (x, v)
    }

  } ensuring (_ match {
    case (a, b) => -10 <= a && a <= 10 && -10 <= b && b <= 10   
  })

  @loopbound(10)
  def rk4Rec(x: Real, v: Real, i: Int): (Real, Real) = {
    require(loopCounter(i) && -10.0 <= x && x <= 10.0 && -10.0 <= v && v <= 10.0 &&
      0.5*(v*v + 2.3*x*x) <= 115)
 
    if (i < 100) {

      val k: Real = 2.3
      val h: Real = 0.1

      val k1x = v
      val k1v = -k*x

      val k2x = v - k*h*x/2.0
      val k2v = -k*x - h*k*v/2.0

      val k3x = v - k*h*x/2.0 - h*h*k*v/4.0
      val k3v = -k*x - k*h*v/2.0 + k*k*h*h*x/4.0

      val k4x = v - k*h*x - k*h*h*v/2.0 + k*k*h*h*h*x/4.0
      val k4v = -k*x - k*h*v + k*k*h*h*x/2.0 + h*h*h*k*k*v/4.0
      
      val x1 = x + h*(k1x + 2.0*k2x + 2*k3x + k4x)/6.0
      val v1 = v + h*(k1v + 2.0*k2v + 2*k3v + k4v)/6.0

      rk4Rec(x1, v1, i + 1)

    } else {
      (x, v)
    }

  } ensuring (_ match {
    case (a, b) => -10 <= a && a <= 10 && -10 <= b && b <= 10   
  })


  @loopbound(10)
  def euler(x: Real, v: Real): (Real, Real) = {
    require(-10.0 <= x && x <= 10.0 && -10.0 <= v && v <= 10.0 &&
      0.5*(v*v + 2.3*x*x) <= 115)
    iterate (x, v) {
      x <== x + 0.1 * v
      v <== v - 2.3 * 0.1 * x
    }
  } ensuring (_ match {
    case (a, b) => -10 <= a && a <= 10 && -10 <= b && b <= 10   
  })

  @loopbound(10)
  def rk2(x: Real, v: Real): (Real, Real) = {
    require(-10.0 <= x && x <= 10.0 && -10.0 <= v && v <= 10.0 &&
      0.5*(v*v + 2.3*x*x) <= 115)

    iterate (x, v) {

      //val k: Real = 2.3
      //val h: Real = 0.1
      
      //val dx = 0.1 * (v + (-2.3*x*0.1/2))
      //val dv = 0.1 * (-2.3)* (x + v*0.1/2)

      x <== x + 0.1 * (v + (-2.3*x*0.1/2))
      v <== v + 0.1 * (-2.3)* (x + v*0.1/2)
    }

  } ensuring (_ match {
    case (a, b) => -10 <= a && a <= 10 && -10 <= b && b <= 10   
  })

  @loopbound(10)
  def rk4(x: Real, v: Real): (Real, Real) = {
    require(-10.0 <= x && x <= 10.0 && -10.0 <= v && v <= 10.0 &&
      0.5*(v*v + 2.3*x*x) <= 115)
 
    iterate (x, v) {

      /*val k: Real = 2.3
      val h: Real = 0.1

      val k1x = v
      val k1v = -2.3*x

      val k2x = v - 2.3*0.1*x/2.0
      val k2v = -2.3*x - 0.1*2.3*v/2.0

      val k3x = v - 2.3*0.1*x/2.0 - 0.1*0.1*2.3*v/4.0
      val k3v = -2.3*x - 2.3*0.1*v/2.0 + 2.3*2.3*0.1*0.1*x/4.0

      val k4x = v - 2.3*0.1*x - 2.3*0.1*0.1*v/2.0 + 2.3*2.3*0.1*0.1*0.1*x/4.0
      val k4v = -2.3*x - 2.3*0.1*v + 2.3*2.3*0.1*0.1*x/2.0 + 0.1*0.1*0.1*2.3*2.3*v/4.0
      */
      x <== x + 0.1*(
        v +
        2.0*(v - 2.3*0.1*x/2.0) +
        2.0*(v - 2.3*0.1*x/2.0 - 0.1*0.1*2.3*v/4.0) +
        (v - 2.3*0.1*x - 2.3*0.1*0.1*v/2.0 + 2.3*2.3*0.1*0.1*0.1*x/4.0) )/6.0
      v <== v + 0.1*(
        -2.3*x + 
        2.0*(-2.3*x - 0.1*2.3*v/2.0) +
        2.0*(-2.3*x - 2.3*0.1*v/2.0 + 2.3*2.3*0.1*0.1*x/4.0) +
        -2.3*x - 2.3*0.1*v + 2.3*2.3*0.1*0.1*x/2.0 + 0.1*0.1*0.1*2.3*2.3*v/4.0)/6.0
    }

  } ensuring (_ match {
    case (a, b) => -10 <= a && a <= 10 && -10 <= b && b <= 10   
  })


/*  @loopbound(10)
  def euler(x: Real, v: Real): (Real, Real) = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
    iterate (x, v) {
      x <== x + 0.1 * v
      v <== v - 2.3 * 0.1 * x
    }
  } ensuring (_ match {
    case (a, b) => -10 <= a && a <= 10 && -10 <= b && b <= 10   
  })


  def rungeKutta2(x: Real, v: Real): (Real, Real) = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)

    iterate (x, v) {

      val k: Real = 2.3
      val h: Real = 0.1
      
      val dx = h * (v + (-k*x*h/2))
      val dv = h * (-k)* (x + v*h/2)

      x <== x + dx
      v <== v + dv
    }

  } ensuring (_ match {
    case (a, b) => -10 <= a && a <= 10 && -10 <= b && b <= 10   
  })


  def rungeKutta4(x: Real, v: Real): (Real, Real) = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
 
    iterate (x, v) {

      val k: Real = 2.3
      val h: Real = 0.1

      val k1x = v
      val k1v = -k*x

      val k2x = v - k*h*x/2.0
      val k2v = -k*x - h*k*v/2.0

      val k3x = v - k*h*x/2.0 - h*h*k*v/4.0
      val k3v = -k*x - k*h*v/2.0 + k*k*h*h*x/4.0

      val k4x = v - k*h*x - k*h*h*v/2.0 + k*k*h*h*h*x/4.0
      val k4v = -k*x - k*h*v + k*k*h*h*x/2.0 + h*h*h*k*k*v/4.0
      
      x <== x + h*(k1x + 2.0*k2x + 2*k3x + k4x)/6.0
      v <== v + h*(k1v + 2.0*k2v + 2*k3v + k4v)/6.0
    }

  } ensuring (_ match {
    case (a, b) => -10 <= a && a <= 10 && -10 <= b && b <= 10   
  })*/


  // k = 2.3, dt = 0.1
  /*def eulerFor(i: Int, x: Real, v: Real): (Real, Real) = {
    require(-10.0 <= x && x <= 10.0 && -10.0 <= v && v <= 10.0)
    if (i > 1000) {
      (x, v)
    } else {
      val xn = x + 0.1 * v
      val vn = v - 2.3 * 0.1 * x
      eulerFor(i + 1, xn, vn)
    }
  } ensuring (res => x <= 10.0)

  def eulerBack(i: Int, x: Real, v: Real): (Real, Real) = {
    require(-10.0 <= x && x <= 10.0 && -10.0 <= v && v <= 10.0)
    if (i > 1000) {
      (x, v)
    } else {
      val (xn, vn) = eulerBack(i + 1, x, v)
      (xn + 0.1 * vn, vn - 2.3 * 0.1 * xn) 
    }
  } ensuring (res => 10.0 <= x && x <= 10.0 && 10.0 <= v && v <= 10.0)
  */
}