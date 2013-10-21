
import leon.Real
import Real._


object Triangles {

  def triangle(a: Real, b: Real, c: Real): Real = {
    require(a >< (1.0, 9.0) && b >< (1.0, 9.0) && c >< (1.0, 9.0) &&
      a +/- 1e-10 && b +/- 1e-10 && c +/- 1e-10 &&
      a + b > c + 0.000001 && a + c > b + 0.000001 && b + c > a + 0.000001)

    val s = (a + b + c)/2.0
    sqrt(s * (s - a) * (s - b) * (s - c))
  }
  
}
