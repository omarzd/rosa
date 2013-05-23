
import leon.Real
import Real._


object Micro {

  def f1(x: Real): Real = {
    require(0 <= x && x <= 2.3)
    x*x  
  } ensuring (res => res <= 5.3)


  def f2(x: Real): Real = {
    require(0 <= x && x <= 3 && noise(x) <= 1e-9)
    x*x
  } ensuring (res => res <= 5.3 && noise(res) <= 1e-8)
  
  def f3(x: Real): Real = {
    require(0 <= x && x <= 2.3 && roundoff(x))
    x*x
  } ensuring (res => res <= 5.3 && noise(res) <= 1e-8)


  def f4(x: Real): Real = {
    require(0 <= x && x <= 2.3)
    if (x * x <= 0) {
      2*x
    } else {
      5*x  
    }
  } ensuring (res => res >= 0)

  def f5(x: Real): Real = {
    require(0 <= x && x <= 2.3 && noise(x) <= 1e-7)
    if (x * x <= 0) {
      2*x
    } else {
      5*x  
    }
  } ensuring (res => res >= 0 && noise(res) <= 1e-5)


  def f6(x: Real): Real = {
    require(0 <= x && x <= 2.3 && roundoff(x))
    if (x * x <= 0) {
      2*x
    } else {
      5*x  
    }
  } ensuring (res => res >= 0 && noise(res) <= 1e-15)
  
}
