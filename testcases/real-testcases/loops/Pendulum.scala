import leon.real._
import RealOps._
import annotations._

object Pendulum {

  //m = 1, k = 2.3 => w = sqrt(2.3)
  @loopbound(10)
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
}