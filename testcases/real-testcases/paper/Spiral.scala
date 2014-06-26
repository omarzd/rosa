import leon.real._
import RealOps._


object Spiral {

  def spiral(x: Real, y: Real, k: LoopCounter): (Real, Real) = {
    require(-10 <= x && x <= 10 && -10 <= y && y <= 10 &&
          -10 <= ~x && ~x <= 10 && -10 <= ~y && ~y <= 10 &&
          x*x + y*y < 100)// && initialErrors(x +/- 1e-9 && y +/- 1e-9))
    
    if (k < 50) {

      val x1 = (9.9*x - y)/10
      val y1 = (9.9*y + x)/10
      spiral(x1,y1, k++)
    
    } else {
      (x, y)
    }

  } ensuring (_ match {
    case (a, b) => -10 <= ~a && ~a <= 10 && -10 <= ~b && ~b <= 10 &&
      -10 <= a && a <= 10 && -10 <= b && b <= 10
  })

}