

/**
  These benchmarks come from the fixed-point aritmetic domain.
 */
object Fixedpoint {

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


  def jetEngine(x1: Double, x2: Double): Double = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5)
    x1 + ((2*x1*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1))*
    ((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1) - 3) + x1*x1*(4*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  } ensuring (res => res >= -56020.0)



}
