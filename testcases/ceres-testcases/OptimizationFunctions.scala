
import leon.Real
import Real._


/**
  Functions used in testing optimization procedures, at least according to
  Wikipedia: http://en.wikipedia.org/wiki/Test_functions_for_optimization
 */
object OptimizationFunctions {

  // The input and output bounds are kind of random.

  // Sim: [13.11833645149913,31629066.12856068]    (4.470348358154297E-8)
  def beales(x: Real, y: Real): Real = {
    require(-4 <= x && x <= 0.5 && 1.5 <= y && y <= 4.45 && roundoff(x) && roundoff(y))
    (1.5 - x + x*y)*(1.5 - x + x*y) +
    (2.25 - x + x*y*(x*y))*(2.25 - x + x*y*(x*y)) +
    (2.625 - x + x*y*(x*y)*(x*y))*(2.625 - x + x*y*(x*y)*(x*y))
  } ensuring (res => 13.0 <= res && res <= 31629067.0 && noise(res, 1e-7))

  //Sim: [14.01916781064652,185495053.2162193]    (2.384185791015625E-7)
  def beales2(x: Real, y: Real): Real = {
    require(-5 <= x && x <= 2.5 && 2.5 <= y && y <= 4.78 && roundoff(x) && roundoff(y))
    (1.5 - x + x*y)*(1.5 - x + x*y) +
    (2.25 - x + x*y*(x*y))*(2.25 - x + x*y*(x*y)) +
    (2.625 - x + x*y*(x*y)*(x*y))*(2.625 - x + x*y*(x*y)*(x*y))
  } ensuring (res => 14.0 <= res && res <= 185495100.0 && noise(res, 1e-6))

  // Sim: [0.2860857182376199,64239542.37063869]    (8.940696716308594E-8)
  def beales3(x: Real, y: Real): Real = {
    require(-2 <= x && x <= 4.5 && 0.2 <= y && y <= 4.45 && roundoff(x) && roundoff(y))
    (1.5 - x + x*y)*(1.5 - x + x*y) +
    (2.25 - x + x*y*(x*y))*(2.25 - x + x*y*(x*y)) +
    (2.625 - x + x*y*(x*y)*(x*y))*(2.625 - x + x*y*(x*y)*(x*y))
  } ensuring (res => 0.28 <= res && res <= 64239600.0 && noise(res, 1e-7))


  // Sim: [180.1158417843523,679.1975462951999]    (3.410605131648481E-13)
  def booths(x: Real, y: Real): Real = {
    require(-9 <= x && x <= -5 && 1 <= y && y <= 3 && roundoff(x) && roundoff(y))
    (x + 2*y -7)*(x + 2*y -7) + (2*x + y -5)*(2*x + y -5)
  } ensuring (res => 180.0 <= res && res <= 678.0 && noise(res, 1e-12))

  // Sim: [0.0003442945751460915,1826.126764300354]    (6.821210263296962E-13)
  def booths2(x: Real, y: Real): Real = {
    require(-13 <= x && x <= 2 && -3 <= y && y <= 7.6 && roundoff(x) && roundoff(y))
    (x + 2*y -7)*(x + 2*y -7) + (2*x + y -5)*(2*x + y -5)
  } ensuring (res => 0.0 <= res && res <= 1827.0 && noise(res, 1e-12))

  // Sim: [1.802273718141507,784.8745892544846]    (3.410605131648481E-13)
  def booths3(x: Real, y: Real): Real = {
    require(-5 <= x && x <= 6.7 && 4 <= y && y <= 10.5 && roundoff(x) && roundoff(y))
    (x + 2*y -7)*(x + 2*y -7) + (2*x + y -5)*(2*x + y -5)
  } ensuring (res => 1.8 <= res && res <= 785.0 && noise(res, 1e-12))


  // Sim: [8.493308609645456e-05,2047.524374981617]    (2.2737367544323206E-12)
  def camel(x: Real, y: Real): Real = {
    require(-5 <= x && x <= 5 && -5 <= y && y <= 5 && roundoff(x) && roundoff(y))
    2*x*x - 1.05*x*x*x*x + (x*x*x*x*x*x)/6 + x*y + y*y
  } ensuring (res => 0.0 <= res && res <= 2048.0 && noise(res, 1e-11))

  // Sim: [6.728205373144213e-05,1163600.441136090]    (9.313225746154785E-10)
  def camel2(x: Real, y: Real): Real = {
    require(-13.9 <= x && x <= 7.98 && -12.8 <= y && y <= 8.9 && roundoff(x) && roundoff(y))
    2*x*x - 1.05*x*x*x*x + (x*x*x*x*x*x)/6 + x*y + y*y
  } ensuring (res => 6.7 <= res && res <= 1163650.0 && noise(res, 1e-8))

  // Sim: [1.335997722024297e-05,143776.6793834211]    (1.4551915228366852E-10)
  def camel3(x: Real, y: Real): Real = {
    require(-2.4 <= x && x <= 9.86 && -1.2 <= y && y <= 14.78 && roundoff(x) && roundoff(y))
    2*x*x - 1.05*x*x*x*x + (x*x*x*x*x*x)/6 + x*y + y*y
  } ensuring (res => 1.3 <= res && res <= 143777.0 && noise(res, 1e-8))


  // Sim: [1215.987918907554,351618.8163690719]    (4.0745362639427185E-10)
  // Does not time out!
  def goldstein(x: Real, y: Real): Real = {
    require(-1.5 <= x && x <= 0.5 && 0.5 <= y && y <= 1.5 && roundoff(x, y))
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

  // Sim: [9.173973378642248,36.33989801853660]    (1.4210854715202004E-14)
  def matyas(x: Real, y: Real): Real  = {
    require(-9 <= x && x <= -5 && 1 <= y && y <= 3 && roundoff(x) && roundoff(y))
    0.26*(x*x + y*y) - 0.48*x*y
  } ensuring (res => 9.1 <= res && res <= 36.4 && noise(res, 1e-13))

  // Sim: [1.178824621943839,176.6983532634135]    (5.6843418860808015E-14)
  def matyas2(x: Real, y: Real): Real  = {
    require(-19 <= x && x <= -3 && -1 <= y && y <= 7.5 && roundoff(x) && roundoff(y))
    0.26*(x*x + y*y) - 0.48*x*y
  } ensuring (res => 1.1 <= res && res <= 177.0 && noise(res, 1e-13))

  // Sim: [1.502261526737385e-06,70.06356062864200]    (2.8421709430404007E-14)
  def matyas3(x: Real, y: Real): Real  = {
    require(-3.4 <= x && x <= 5 && -11.7 <= y && y <= 1 && roundoff(x) && roundoff(y))
    0.26*(x*x + y*y) - 0.48*x*y
  } ensuring (res => 1.5 <= res && res <= 70.1 && noise(res, 1e-13))


  // Sim: [36.21337199193115,486842455.6749934]    (2.384185791015625E-7)
  def motzkin(x: Real, y: Real, z: Real): Real = {
    require(-5.6 <= x && x <= 1.3 && 45.3 <= y && y <= 63.0 &&
            3.2 <= z && z <= 15.7 && roundoff(x) && roundoff(y) && roundoff(z))
    z*z*z + x*x*(y*y) * (z*z + y*y - 3*z*z)
  } ensuring (res => 36.0 <= res && res <= 486842460.0 && noise(res, 1e-6))

  def motzkin2(x: Real, y: Real, z: Real): Real = {
    require(-9.6 <= x && x <= 3.3 && 25.3 <= y && y <= 56.0 &&
            -3.2 <= z && z <= 25.7 && roundoff(x, y, z))
    z*z*z + x*x*(y*y) * (z*z + y*y - 3*z*z)
  } ensuring (res => res >= -56020.0)

  // Sim: [-31.98118558979185,180335165.7024984]    (1.1920928955078125E-7)
  def motzkin3(x: Real, y: Real, z: Real): Real = {
    require(-2.6 <= x && x <= 7.3 && 25.3 <= y && y <= 43.0 &&
            -3.2 <= z && z <= 10.7 && roundoff(x) && roundoff(y) && roundoff(z))
    z*z*z + x*x*(y*y) * (z*z + y*y - 3*z*z)
  } ensuring (res => -32.0 <= res && res <= 180335170.0 && noise(res, 1e-6))

}

