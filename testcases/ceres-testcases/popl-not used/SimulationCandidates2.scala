import leon.Real
import Real._

object Sine {

  def newton1_2(in: Real): Real = {
    require(in > -0.2 && in < 0.2)

    val x1 = in - (in - (in*in*in)/6.0 + (in*in*in*in*in)/120.0 + (in*in*in*in*in*in*in)/5040.0) / (1 - (in*in)/2.0 + (in*in*in*in)/24.0 + (in*in*in*in*in*in)/720.0)
    x1 - (x1 - (x1*x1*x1)/6.0 + (x1*x1*x1*x1*x1)/120.0 + (x1*x1*x1*x1*x1*x1*x1)/5040.0) / (1 - (x1*x1)/2.0 + (x1*x1*x1*x1)/24.0 + (x1*x1*x1*x1*x1*x1)/720.0)

  }
  // valid
  def newton2_2(in: Real): Real = {
    require(in > -0.4 && in < 0.4)
    
    val x1 = in - (in - (in*in*in)/6.0 + (in*in*in*in*in)/120.0 + (in*in*in*in*in*in*in)/5040.0) / (1 - (in*in)/2.0 + (in*in*in*in)/24.0 + (in*in*in*in*in*in)/720.0)
    x1 - (x1 - (x1*x1*x1)/6.0 + (x1*x1*x1*x1*x1)/120.0 + (x1*x1*x1*x1*x1*x1*x1)/5040.0) / (1 - (x1*x1)/2.0 + (x1*x1*x1*x1)/24.0 + (x1*x1*x1*x1*x1*x1)/720.0)
  }
  // valid
  def newton3_2(in: Real): Real = {
    require(in > -0.6 && in < 0.6)
    
    val x1 = in - (in - (in*in*in)/6.0 + (in*in*in*in*in)/120.0 + (in*in*in*in*in*in*in)/5040.0) / (1 - (in*in)/2.0 + (in*in*in*in)/24.0 + (in*in*in*in*in*in)/720.0)
    x1 - (x1 - (x1*x1*x1)/6.0 + (x1*x1*x1*x1*x1)/120.0 + (x1*x1*x1*x1*x1*x1*x1)/5040.0) / (1 - (x1*x1)/2.0 + (x1*x1*x1*x1)/24.0 + (x1*x1*x1*x1*x1*x1)/720.0)
  }
  // valid
  def newton4_2(in: Real): Real = {
    require(in > -0.8 && in < 0.8)
    
    val x1 = in - (in - (in*in*in)/6.0 + (in*in*in*in*in)/120.0 + (in*in*in*in*in*in*in)/5040.0) / (1 - (in*in)/2.0 + (in*in*in*in)/24.0 + (in*in*in*in*in*in)/720.0)
    x1 - (x1 - (x1*x1*x1)/6.0 + (x1*x1*x1*x1*x1)/120.0 + (x1*x1*x1*x1*x1*x1*x1)/5040.0) / (1 - (x1*x1)/2.0 + (x1*x1*x1*x1)/24.0 + (x1*x1*x1*x1*x1*x1)/720.0)
  }
  // valid
  def newton5_2(in: Real): Real = {
    require(in > -1.0 && in < 1.0)
    
    val x1 = in - (in - (in*in*in)/6.0 + (in*in*in*in*in)/120.0 + (in*in*in*in*in*in*in)/5040.0) / (1 - (in*in)/2.0 + (in*in*in*in)/24.0 + (in*in*in*in*in*in)/720.0)
    x1 - (x1 - (x1*x1*x1)/6.0 + (x1*x1*x1*x1*x1)/120.0 + (x1*x1*x1*x1*x1*x1*x1)/5040.0) / (1 - (x1*x1)/2.0 + (x1*x1*x1*x1)/24.0 + (x1*x1*x1*x1*x1*x1)/720.0)
  }
  // not valid
  def newton6_2(in: Real): Real = {
    require(in > -1.2 && in < 1.2)
    
    val x1 = in - (in - (in*in*in)/6.0 + (in*in*in*in*in)/120.0 + (in*in*in*in*in*in*in)/5040.0) / (1 - (in*in)/2.0 + (in*in*in*in)/24.0 + (in*in*in*in*in*in)/720.0)
    x1 - (x1 - (x1*x1*x1)/6.0 + (x1*x1*x1*x1*x1)/120.0 + (x1*x1*x1*x1*x1*x1*x1)/5040.0) / (1 - (x1*x1)/2.0 + (x1*x1*x1*x1)/24.0 + (x1*x1*x1*x1*x1*x1)/720.0)
  }
  // not valid
  def newton7_2(in: Real): Real = {
    require(in > -1.4 && in < 1.4)
    
    val x1 = in - (in - (in*in*in)/6.0 + (in*in*in*in*in)/120.0 + (in*in*in*in*in*in*in)/5040.0) / (1 - (in*in)/2.0 + (in*in*in*in)/24.0 + (in*in*in*in*in*in)/720.0)
    x1 - (x1 - (x1*x1*x1)/6.0 + (x1*x1*x1*x1*x1)/120.0 + (x1*x1*x1*x1*x1*x1*x1)/5040.0) / (1 - (x1*x1)/2.0 + (x1*x1*x1*x1)/24.0 + (x1*x1*x1*x1*x1*x1)/720.0)
  }
  // not valid
  def newton8_2(in: Real): Real = {
    require(in > -2.0 && in < 2.0)
    
    val x1 = in - (in - (in*in*in)/6.0 + (in*in*in*in*in)/120.0 + (in*in*in*in*in*in*in)/5040.0) / (1 - (in*in)/2.0 + (in*in*in*in)/24.0 + (in*in*in*in*in*in)/720.0)
    x1 - (x1 - (x1*x1*x1)/6.0 + (x1*x1*x1*x1*x1)/120.0 + (x1*x1*x1*x1*x1*x1*x1)/5040.0) / (1 - (x1*x1)/2.0 + (x1*x1*x1*x1)/24.0 + (x1*x1*x1*x1*x1*x1)/720.0)
  }

}
