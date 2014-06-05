import leon.real._
import RealOps._

object Piecewise2D {

  //These are various approximations to this function: f[x_, y_] := x y /(x^2 + y^2 + 0.3)

  // looking at the picture, the error should be about ~1.0
  def linear(x: Real, y: Real): Real = {
    require(-4 <= x && x <= 4 && -4 <= y && y <= 4)

    if (x <= 0) {
      if (y <= 0) {
        -0.495356 - 0.123839*x - 0.1233839*y
      } else {
        0.495356 + 0.123839*x - 0.1233839*y
      }

    } else { // x >= 0
      if (y <= 0) {
        0.495356 - 0.123839*x + 0.1233839*y
      } else {
        -0.495356 + 0.123839*x + 0.1233839*y
      }
    }

  } ensuring ( res => res +/- 1e-9 )


  def quadraticFit(x: Real, y: Real): Real = {
    require(-4 <= x && x <= 4 && -4 <= y && y <= 4)// && x +/- 1e-8 && y +/- 1e-8)

    if (x <= 0) {
      if (y <= 0) {
        -0.0495178 - 0.188656*x - 0.0502969*x*x - 0.188656*y + 0.0384002*x*y - 0.0502969*y*y
      } else {
        0.0495178 + 0.188656*x + 0.0502969*x*x - 0.188656*y + 0.0384002*x*y + 0.0502969*y*y
      }

    } else { // x >= 0
      if (y <= 0) {
        0.0495178 - 0.188656*x + 0.0502969*x*x + 0.188656*y + 0.0384002*x*y + 0.0502969*y*y
      } else {
        -0.0495178 + 0.188656*x - 0.0502969*x*x + 0.188656*y + 0.0384002*x*y - 0.0502969*y*y
      }
    }
  } ensuring ( res => res +/- 1e-9 )
}
