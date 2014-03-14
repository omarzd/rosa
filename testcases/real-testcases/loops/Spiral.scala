import leon.real._
import RealOps._
import realannotations._

object Spiral {

  @loopbound(2)
  def spiralReal(x: Real, y: Real): (Real, Real) = {
    require(x*x + y*y < 100 && -10 <= x && x <= 10 && -10 <= y && y <= 10)

    iterate(x, y) {
      x <== (9.9*x - y) / 10.0
      y <== (9.9*y + x) / 10.0
    }

  } ensuring (_ match {
    case (a, b) => -10 <= a && a <= 10 && -10 <= b && b <= 10
  })

  /*@loopbound(2)
  def spiralReal(x: Real, y: Real): (Real, Real) = {
    require(x*x + y*y < 100 && -10 <= x && x <= 10 && -10 <= y && y <= 10)

    iterate(x, y) {
      x <== (9.9*x - y) / 10.0
      y <== (9.9*y + x) / 10.0
    }

  } ensuring (_ match {
    case (a, b) => -10 <= a && a <= 10 && -10 <= b && b <= 10
  })*/

  /*@loopbound(5)
  def spiralBoth(x: Real, y: Real): (Real, Real) = {
    require(x*x + y*y < 100 && -10 <= x && x <= 10 && -10 <= y && y <= 10)

    iterate(x, y) {
      x <== (9.9*x - y) / 10.0
      y <== (9.9*y + x) / 10.0
    }

  } ensuring (_ match {
    case (a, b) => -10 <= a && a <= 10 && -10 <= b && b <= 10 &&
      -10 <= ~a && ~a <= 10 && -10 <= ~b && ~b <= 10
  })*/


  /*def spiralBack(x: Real, y: Real, k: Int): (Real, Real) = {
    require(0 <= k && k <= 10 && x*x + y*y < 100 && -10 <= x && x <= 10 &&
            -10 <= y && y <= 10)
    
    if (k > 1) {
      val (xn, yn) = spiralBack(x, y, k - 1)

      val x1 = (9.9*xn - yn)/10
      val y1 = (9.9*yn + xn)/10
      (x1,y1)

    } else {
      (x, y)
    }

  } ensuring (_ match {
    case (a, b) => -10 < a && a < 10 && -10 < b && b < 10 //&& a +/- 1e-12 && b +/- 1e-12
  })*/

  /*def spiralForward(x: Real, y: Real, k: Real): (Real, Real) = {
    require(0 <= k && k <= 10 && x*x + y*y < 100 && -10 <= x && x <= 10 &&
            -10 <= y && y <= 10)
    
    // k should be an integer
    if (k > 1.1) {
      val x1 = (9.9*x - y)/10
      val y1 = (9.9*y + x)/10
      spiralForward(x1,y1,k-1)
    } else {
      (x, y)
    }

  } ensuring (_ match {
    case (a, b) => -10 < a && a < 10 && -10 < b && b < 10 //&& a +/- 1e-12 && b +/- 1e-12
  })*/
}