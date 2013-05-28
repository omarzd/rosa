
import leon.Real
import Real._


/**
  Functions used in testing optimization procedures, at least according to
  Wikipedia: http://en.wikipedia.org/wiki/Test_functions_for_optimization
 */
object OptimizationFunctions {

  // The input and output bounds are kind of random.

  def beales(x: Real, y: Real): Real = {
    require(-4 <= x && x <= 0.5 && 1.5 <= y && y <= 4.45)
    (1.5 - x + x*y)*(1.5 - x + x*y) +
    (2.25 - x + x*y*(x*y))*(2.25 - x + x*y*(x*y)) +
    (2.625 - x + x*y*(x*y)*(x*y))*(2.625 - x + x*y*(x*y)*(x*y))
  } ensuring (res => res >= -56020.0)

  def beales2(x: Real, y: Real): Real = {
    require(-5 <= x && x <= 2.5 && 2.5 <= y && y <= 4.78)
    (1.5 - x + x*y)*(1.5 - x + x*y) +
    (2.25 - x + x*y*(x*y))*(2.25 - x + x*y*(x*y)) +
    (2.625 - x + x*y*(x*y)*(x*y))*(2.625 - x + x*y*(x*y)*(x*y))
  } ensuring (res => res >= -56020.0)
 
  def beales3(x: Real, y: Real): Real = {
    require(-2 <= x && x <= 4.5 && 0.2 <= y && y <= 4.45)
    (1.5 - x + x*y)*(1.5 - x + x*y) +
    (2.25 - x + x*y*(x*y))*(2.25 - x + x*y*(x*y)) +
    (2.625 - x + x*y*(x*y)*(x*y))*(2.625 - x + x*y*(x*y)*(x*y))
  } ensuring (res => res >= -56020.0)
 


  def booths(x: Real, y: Real): Real = {
    require(-9 <= x && x <= -5 && 1 <= y && y <= 3)
    (x + 2*y -7)*(x + 2*y -7) + (2*x + y -5)*(2*x + y -5)
  } ensuring (res => res >= -56020.0)

  def booths2(x: Real, y: Real): Real = {
    require(-13 <= x && x <= 2 && -3 <= y && y <= 7.6)
    (x + 2*y -7)*(x + 2*y -7) + (2*x + y -5)*(2*x + y -5)
  } ensuring (res => res >= -56020.0)
  
  def booths3(x: Real, y: Real): Real = {
    require(-5 <= x && x <= 6.7 && 4 <= y && y <= 10.5)
    (x + 2*y -7)*(x + 2*y -7) + (2*x + y -5)*(2*x + y -5)
  } ensuring (res => res >= -56020.0)



  def camel(x: Real, y: Real): Real = {
    require(-5 <= x && x <= 5 && -5 <= y && y <= 5)
    2*x*x - 1.05*x*x*x*x + (x*x*x*x*x*x)/6 + x*y + y*y
  } ensuring (res => res >= -56020.0)

  def camel2(x: Real, y: Real): Real = {
    require(-13.9 <= x && x <= 7.98 && -12.8 <= y && y <= 8.9)
    2*x*x - 1.05*x*x*x*x + (x*x*x*x*x*x)/6 + x*y + y*y
  } ensuring (res => res >= -56020.0)
  
  def camel3(x: Real, y: Real): Real = {
    require(-2.4 <= x && x <= 9.86 && -1.2 <= y && y <= 14.78)
    2*x*x - 1.05*x*x*x*x + (x*x*x*x*x*x)/6 + x*y + y*y
  } ensuring (res => res >= -56020.0)



  def goldstein(x: Real, y: Real): Real = {
    require(-1.5 <= x && x <= 0.5 && 0.5 <= y && y <= 1.5)
    (1 + (x + y + 1)*(x + y + 1) *(19 - 14*x + 3*x*x - 14*y + 6*x*y + 3*y*y)) *
    (30 + (2*x - 3*y)*(2*x - 3*y) * (18 - 32*x + 12*x*x +48*y - 36*x*y + 27*y*y))
  } ensuring (res => res >= -56020.0)
  
  // This gets a RationalCannotBeCastToIntsException:
  //-2.56 <= x && x <= 7.5 && -3.56 <= y && y <= 6.55
  /*def goldstein2(x: Real, y: Real): Real = {
    require(-1.76 <= x && x <= 4.5 && -1.56 <= y && y <= 4.55)
    (1 + (x + y + 1)*(x + y + 1) *(19 - 14*x + 3*x*x - 14*y + 6*x*y + 3*y*y)) *
    (30 + (2*x - 3*y)*(2*x - 3*y) * (18 - 32*x + 12*x*x +48*y - 36*x*y + 27*y*y))
  } ensuring (res => res >= -56020.0)
  
  def goldstein3(x: Real, y: Real): Real = {
    require(-0.5 <= x && x <= 5.5 && -3.5 <= y && y <= -1.5)
    (1 + (x + y + 1)*(x + y + 1) *(19 - 14*x + 3*x*x - 14*y + 6*x*y + 3*y*y)) *
    (30 + (2*x - 3*y)*(2*x - 3*y) * (18 - 32*x + 12*x*x +48*y - 36*x*y + 27*y*y))
  } ensuring (res => res >= -56020.0)
  */


  def matyas(x: Real, y: Real): Real  = {
    require(-9 <= x && x <= -5 && 1 <= y && y <= 3)
    0.26*(x*x + y*y) - 0.48*x*y
  } ensuring (res => res >= -56020.0)

  def matyas2(x: Real, y: Real): Real  = {
    require(-19 <= x && x <= -3 && -1 <= y && y <= 7.5)
    0.26*(x*x + y*y) - 0.48*x*y
  } ensuring (res => res >= -56020.0)
  
  def matyas3(x: Real, y: Real): Real  = {
    require(-3.4 <= x && x <= 5 && -11.7 <= y && y <= 1)
    0.26*(x*x + y*y) - 0.48*x*y
  } ensuring (res => res >= -56020.0)
  


  def motzkin(x: Real, y: Real, z: Real): Real = {
    require(-5.6 <= x && x <= 1.3 && 45.3 <= y && y <= 63.0 &&
            3.2 <= z && z <= 15.7)
    z*z*z + x*x*(y*y) * (z*z + y*y - 3*z*z)
  } ensuring (res => res >= -56020.0)
 
  /*def motzkin2(x: Real, y: Real, z: Real): Real = {
    require(-9.6 <= x && x <= 3.3 && 25.3 <= y && y <= 83.0 &&
            -3.2 <= z && z <= 45.7)
    z*z*z + x*x*(y*y) * (z*z + y*y - 3*z*z)
  } ensuring (res => res >= -56020.0)*/

  def motzkin3(x: Real, y: Real, z: Real): Real = {
    require(-2.6 <= x && x <= 7.3 && 25.3 <= y && y <= 43.0 &&
            -3.2 <= z && z <= 10.7)
    z*z*z + x*x*(y*y) * (z*z + y*y - 3*z*z)
  } ensuring (res => res >= -56020.0)

}

