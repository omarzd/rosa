
import leon.NumericUtils._


object Debug {
  
  def rigidBody2(x1: Double, x2: Double, x3: Double): Double = {
    require(x1 <= 15 && x1 >= -15 && x2 <= 15 && x2 >= -15 &&
            x3 <= 15 && x3 >= -15)
    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  } ensuring (res => res >= -32000.0)
  
 
  /*def test(x: Double): Double = {
    require(x*x == 2)
    x
  } ensuring (res => res >= 0)
  */
}
