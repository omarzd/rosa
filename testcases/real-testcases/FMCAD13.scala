import leon.Real
import Real._


object InitialExample {

  def triangle(a: Real, b: Real, c: Real): Real = {
  require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
    a +/- 1e-6 && b +/- 1e-7 && c +/- 1e-5 &&
    a + b > c + 1e-6 && a + c > b + 1e-6 && b + c > a + 1e-6)
    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  }

}