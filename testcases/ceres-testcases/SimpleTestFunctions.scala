import leon.NumericUtils._


// This we should be well capable of handlin'.
object SimpleTestFunctions {

  def rigidBody1(x1: Double, x2: Double, x3: Double): Double = {
    require(x1 <= 15 && x1 >= -15 && x2 <= 15 && x2 >= -15 &&
            x3 <= 15 && x3 >= -15)
    -x1*x2 - 2*x2*x3 - x1 - x3
  } ensuring (res => res <= 705.0)

  def rigidBody2(x1: Double, x2: Double, x3: Double): Double = {
    require(x1 <= 15 && x1 >= -15 && x2 <= 15 && x2 >= -15 &&
            x3 <= 15 && x3 >= -15)
    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  } ensuring (res => res >= -56020.0)


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

  def jetEngine(x1: Double, x2: Double): Double = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5)
    x1 + ((2*x1*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1))*
    ((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1) - 3) + x1*x1*(4*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  } ensuring (res => res >= -56020.0)

  // TODO: check the bounds others find and see if we can show
  // that it is smaller
  def bspline0(u: Double): Double = {
    require(0 <= u && u <= 1)
    (1 - u) * (1 - u) * (1 - u) * (1.0/6.0)
  } ensuring (res => res >= -56020.0)

  def bspline1(u: Double): Double = {
    require(0 <= u && u <= 1)
    (3 * u*u*u - 6 * u*u + 4) * (1/6.0)
  } ensuring (res => res >= -56020.0)

  def bspline2(u: Double): Double = {
    require(0 <= u && u <= 1)
    (-3 * u*u*u  + 3*u*u + 3*u + 1) * (1.0/6)
  } ensuring (res => res >= -56020.0)

  def bspline3(u: Double): Double = {
    require(0 <= u && u <= 1)
    u*u*u * (1.0/6.0)
  } ensuring (res => res >= -56020.0)

  def doppler(u: Double, v: Double, T: Double): Double = {
    require(-100 <= u && u <= 100 && 20 <= v && v <= 20000 &&
     -30 <= T && T <= 50)
    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))
  } ensuring (res => res >= -56020.0)

  def motzkin(x: Double, y: Double, z: Double): Double = {
    require(-5.6 <= x && x <= 1.3 && 45.3 <= y && y <= 63.0 &&
            3.2 <= z && z <= 15.7)
    z*z*z + x*x*(y*y) * (z*z + y*y - 3*z*z)
  } ensuring (res => res >= -56020.0)


}

