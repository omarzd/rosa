
import leon.Real
import Real._


object InitialExample {

  def mainFunction(a: Real): Real = {
    require(4.500005 <= a && a <= 6.5)

    val b = 4.0
    val c = 8.5
    val area = triangleUnstable(a, b, c)
    area
  } ensuring(res => res +/- 1e-11)

  def triangleUnstable(a: Real, b: Real, c: Real): Real = {
    require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
      a + b > c + 0.000001 && a + c > b + 0.000001 && b + c > a + 0.000001)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  }
  
}
