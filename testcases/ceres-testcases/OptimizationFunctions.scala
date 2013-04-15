import leon.NumericUtils._

/**
  Functions used in testing optimization procedures, at least according to
  Wikipedia: http://en.wikipedia.org/wiki/Test_functions_for_optimization
 */
object OptimizationFunctions {

  // The input and output bounds are kind of random.

  def beales(x: Double, y: Double): Double = {
    require(-4 <= x && x <= 0.5 && 1.5 <= y && y <= 4.45)
    (1.5 - x + x*y)*(1.5 - x + x*y) +
    (2.25 - x + x*y*(x*y))*(2.25 - x + x*y*(x*y)) +
    (2.625 - x + x*y*(x*y)*(x*y))*(2.625 - x + x*y*(x*y)*(x*y))
  } ensuring (res => res >= -56020.0)

  def goldstein(x: Double, y: Double): Double = {
    require(-1.5 <= x && x <= 0.5 && 0.5 <= y && y <= 1.5)
    (1 + (x + y + 1)*(x + y + 1) *(19 - 14*x + 3*x*x - 14*y + 6*x*y + 3*y*y)) *
    (30 + (2*x - 3*y)*(2*x - 3*y) * (18 - 32*x + 12*x*x +48*y - 36*x*y + 27*y*y))
  } ensuring (res => res >= -56020.0)

  def booths(x: Double, y: Double): Double = {
    require(-9 <= x && x <= -5 && 1 <= y && y <= 3)
    (x + 2*y -7)*(x + 2*y -7) + (2*x + y -5)*(2*x + y -5)
  } ensuring (res => res >= -56020.0)

  def camel(x: Double, y: Double): Double = {
    require(-5 <= x && x <= 5 && -5 <= y && y <= 5)
    2*x*x - 1.05*x*x*x*x + (x*x*x*x*x*x)/6 + x*y + y*y
  } ensuring (res => res >= -56020.0)

  def matyas(x: Double, y: Double): Double  = {
    require(-9 <= x && x <= -5 && 1 <= y && y <= 3)
    0.26*(x*x + y*y) - 0.48*x*y
  } ensuring (res => res >= -56020.0)

  def motzkin(x: Double, y: Double, z: Double): Double = {
    require(-5.6 <= x && x <= 1.3 && 45.3 <= y && y <= 63.0 &&
            3.2 <= z && z <= 15.7)
    z*z*z + x*x*(y*y) * (z*z + y*y - 3*z*z)
  } ensuring (res => res >= -56020.0)


}

