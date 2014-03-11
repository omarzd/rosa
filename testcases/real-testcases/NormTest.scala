import leon._
import Real._
import RealAnnotations._

object NormTest {

  /*def lipschitzAAEqual(x: Real): Real = {
    require(-10 <= x && x <= 10)

      0.5*x + 3.5
  } ensuring (res => res >= 0)
  */

  def fnc(x: Real, y: Real): Real = {
    require(x*x + y*y < 100 && -10 <= x && x <= 10 && -10 <= y && y <= 10)

      val tmpX = (9.9*x - y) / 10.0
      val tmpY = (9.9*y + x) / 10.0
      (9.9*tmpX - tmpY) / 10.0
      
  } ensuring ( _ >= 0)

  def fnc2(x: Real, y: Real): (Real, Real) = {
    require(x*x + y*y < 100 && -10 <= x && x <= 10 && -10 <= y && y <= 10)

      val tmpX = (9.9*x - y) / 10.0
      val tmpY = (9.9*y + x) / 10.0
      ((9.9*tmpX - tmpY) / 10.0, (9.9*tmpY + tmpX) / 10.0)
      //0.99*tmp
  } ensuring (_ match {
    case (a, b) => -10 <= a && a <= 10 && -10 <= b && b <= 10
  })

}