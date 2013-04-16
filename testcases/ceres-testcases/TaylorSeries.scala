


object TaylorSeries {

  def sin7(x: Double): Double = {
     // for this range the method error is less than 0.000003 (according to Wikipedia)
    require(-1.0 <= x && x <= 1.0)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 - (x*x*x*x*x*x*x)/5040.0
  } ensuring (res => res <= 1.2)

  def cos6(x: Double): Double = {
     // for this range the method error is less than 0.000003 (according to Wikipedia)
    require(-1.0 <= x && x <= 1.0)
    1 - (x*x)/2.0 + (x*x*x*x)/24.0 - (x*x*x*x*x*x)/720.0
  } ensuring (res => res <= 1.2)

  def tan5(x: Double): Double = {
    require(-1.3 <= x && x <= 1.3)
    x + (x*x*x)/3.0 + (2*x*x*x*x*x)/15.0
  } ensuring (res => res <= 3.7)

  def sinh7(x: Double): Double = {
     // for this range the method error is less than 0.000003 (according to Wikipedia)
    require(-1.0 <= x && x <= 1.0)
    x + (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring (res => res <= 1.2)

  def cosh6(x: Double): Double = {
     // for this range the method error is less than 0.000003 (according to Wikipedia)
    require(-1.0 <= x && x <= 1.0)
    1 + (x*x)/2.0 + (x*x*x*x)/24.0 + (x*x*x*x*x*x)/720.0
  } ensuring (res => res <= 1.2)

  def exOverCosx(x: Double): Double = {
    require(-1.5 <= x && x <= 0.8)
    1 + x + x*x + (2*x*x*x)/3.0 + (x*x*x*x)/2.0
  } ensuring (res => res <= 5.0)

}
