
import leon.Real
import Real._


object Micro {

  def f1(x: Real): Real = {
    require(0 <= x && x <= 2.3)
    x+x+x 
  } ensuring (res => res <= 5.3)


  /*def f2(x: Real): Real = {
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
 
  def f7(u: Real, v: Real, T: Real): Real = {
    require(-100 <= u && u <= 100 && 20 <= v && v <= 20000 &&
     -30 <= T && T <= 50)
    val t1 = - (331.4 + 0.6 * T) *v
    val t2 = 331.4 + 0.6*T + u
    val t3 = t2 * t2
    t1 / t3
  } ensuring (res => 0.0 <= res && res <= 138.0)
  
  def f8(u: Real, v: Real, T: Real): Real = {
    require(-100 <= u && u <= 100 && noise(u) <= 1e-6 && 20 <= v && v <= 20000 &&
     noise(v) <= 1e-8 && -30 <= T && T <= 50 && noise(T) <= 0.003)
    val t1 = - (331.4 + 0.6 * T) *v
    val t2 = 331.4 + 0.6*T + u
    val t3 = t2 * t2
    t1 / t3
  } ensuring (res => 0.0 <= res && res <= 138.0 && noise(res) <= 1e-5)

  def f9(x: Real): Real = {
    require(0 <= x && x <= 2.3 && noise(x) <= 1e-14)
    val t1 = x*x
    val t2 = f1(t1)
    t1 + t2
  } ensuring(res => res >= 0 && noise(res) <= 1e-15)

  def f10(x: Real): Real = {
    require(0 <= x && x <= 2.3 && noise(x) <= 1e-14)
    val t1 = x*x
    f1(t1)
  } ensuring(res => res >= 0 && noise(res) <= 1e-15)
  */
}
