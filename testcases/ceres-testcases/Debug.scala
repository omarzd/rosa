
import leon.NumericUtils._


object Debug {

  def camel(x: Double, y: Double): Double = {
    require(-5 <= x && x <= 5 && -5 <= y && y <= 5)
    2*x*x - 1.05*x*x*x*x + (x*x*x*x*x*x)/6 + x*y + y*y
  } ensuring (res => res >= -56020.0)



}
