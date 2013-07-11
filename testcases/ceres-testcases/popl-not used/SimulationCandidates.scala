import leon.Real
import Real._

object Sine {

  def sine1(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  }

  def sqroot1(x: Real): Real = {
    require(x >= 0.0 && x < 1.0)
    1.0 + 0.5*x - 0.125*x*x + 0.0625*x*x*x - 0.0390625*x*x*x*x
  }

  /*def f(x: Real): Real = {
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  }

  def fp(x: Real): Real = {
    1 - (x*x)/2.0 + (x*x*x*x)/24.0 + (x*x*x*x*x*x)/720.0
  }*/

  /*def newton1_1(in: Real): Real = {
    require(in > -0.2 && in < 0.2)

    in - (in - (in*in*in)/6.0 + (in*in*in*in*in)/120.0 + (in*in*in*in*in*in*in)/5040.0) / (1 - (in*in)/2.0 + (in*in*in*in)/24.0 + (in*in*in*in*in*in)/720.0)
  }

  def newton2_1(in: Real): Real = {
    require(in > -0.4 && in < 0.4)
    in - (in - (in*in*in)/6.0 + (in*in*in*in*in)/120.0 + (in*in*in*in*in*in*in)/5040.0) / (1 - (in*in)/2.0 + (in*in*in*in)/24.0 + (in*in*in*in*in*in)/720.0)
  }

  def newton3_1(in: Real): Real = {
    require(in > -0.6 && in < 0.6)
    in - (in - (in*in*in)/6.0 + (in*in*in*in*in)/120.0 + (in*in*in*in*in*in*in)/5040.0) / (1 - (in*in)/2.0 + (in*in*in*in)/24.0 + (in*in*in*in*in*in)/720.0)
  }

  def newton4_1(in: Real): Real = {
    require(in > -0.8 && in < 0.8)
    in - (in - (in*in*in)/6.0 + (in*in*in*in*in)/120.0 + (in*in*in*in*in*in*in)/5040.0) / (1 - (in*in)/2.0 + (in*in*in*in)/24.0 + (in*in*in*in*in*in)/720.0)
  }
  
  def newton5_1(in: Real): Real = {
    require(in > -1.0 && in < 1.0)
    in - (in - (in*in*in)/6.0 + (in*in*in*in*in)/120.0 + (in*in*in*in*in*in*in)/5040.0) / (1 - (in*in)/2.0 + (in*in*in*in)/24.0 + (in*in*in*in*in*in)/720.0)
  }

  def newton6_1(in: Real): Real = {
    require(in > -1.2 && in < 1.2)
    in - (in - (in*in*in)/6.0 + (in*in*in*in*in)/120.0 + (in*in*in*in*in*in*in)/5040.0) / (1 - (in*in)/2.0 + (in*in*in*in)/24.0 + (in*in*in*in*in*in)/720.0)
  }

  def newton7_1(in: Real): Real = {
    require(in > -1.4 && in < 1.4)
    in - (in - (in*in*in)/6.0 + (in*in*in*in*in)/120.0 + (in*in*in*in*in*in*in)/5040.0) / (1 - (in*in)/2.0 + (in*in*in*in)/24.0 + (in*in*in*in*in*in)/720.0)
  }

  def newton8_1(in: Real): Real = {
    require(in > -2.0 && in < 2.0)
    in - (in - (in*in*in)/6.0 + (in*in*in*in*in)/120.0 + (in*in*in*in*in*in*in)/5040.0) / (1 - (in*in)/2.0 + (in*in*in*in)/24.0 + (in*in*in*in*in*in)/720.0)
  }
*/
}