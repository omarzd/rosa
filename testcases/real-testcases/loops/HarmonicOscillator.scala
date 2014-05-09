import leon.real._
import RealOps._
import annotations._

object HarmonicOscillator {

  // TODO: to make this more inductive, include some energy loss term

  /**
    Potential energy: E = 0.5 ( m v^2 + k x^2)
    here: m = 1, k = 2.3, E_initial = 115 (for v=0, x=10)
  */
  @loopbound(10)
  def eulerRec(x: Real, v: Real, i: Int): (Real, Real) = {
    require(loopCounter(i) && -10.0 <= x && x <= 10.0 && -10.0 <= v && v <= 10.0)// &&
      //0.5*(v*v + 2.3*x*x) <= 115)
    
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
    require(loopCounter(i) && -10.0 <= x && x <= 10.0 && -10.0 <= v && v <= 10.0)// &&
       //0.5*(v*v + 2.3*x*x) <= 115)

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
    require(loopCounter(i) && -10.0 <= x && x <= 10.0 && -10.0 <= v && v <= 10.0)// &&
      //0.5*(v*v + 2.3*x*x) <= 115)
 
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

  /*def eulerControl(x: Real, v: Real): (Real, Real) = {
    require(-10.0 <= x && x <= 10.0 && -10.0 <= v && v <= 10.0)
    val x1 = (x + (0.1 * v))
    val v1 = (v - (0.22999999999999998 * x))
    val x2 = (x1 + (0.1 * v1))
    val v2 = (v1 - (0.22999999999999998 * x1))
    val x3 = (x2 + (0.1 * v2))
    val v3 = (v2 - (0.22999999999999998 * x2))
    val x4 = (x3 + (0.1 * v3))
    val v4 = (v3 - (0.22999999999999998 * x3))
    val x5 = (x4 + (0.1 * v4))
    val v5 = (v4 - (0.22999999999999998 * x4))
    val x6 = (x5 + (0.1 * v5))
    val v6 = (v5 - (0.22999999999999998 * x5))
    val x7 = (x6 + (0.1 * v6))
    val v7 = (v6 - (0.22999999999999998 * x6))
    val x8 = (x7 + (0.1 * v7))
    val v8 = (v7 - (0.22999999999999998 * x7))
    val x9 = (x8 + (0.1 * v8))
    val v9 = (v8 - (0.22999999999999998 * x8))
    ((x9 + (0.1 * v9)), (v9 - (0.22999999999999998 * x9)))
  } ensuring (_ match {
    case (a, b) => -10 <= a && a <= 10 && -10 <= b && b <= 10   
  })*/

  /*@loopbound(10)
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
      //val k: Real = 2.3; val h: Real = 0.1
      //val dx = 0.1 * (v + (-2.3*x*0.1/2)); val dv = 0.1 * (-2.3)* (x + v*0.1/2)
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
  */
}