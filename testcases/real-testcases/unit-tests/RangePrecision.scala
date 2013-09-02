
import leon.Real
import Real._

/**
  Equation and initial ranges for doppler from:
  A.B. Kinsman and N. Nicolici. Finite Precision bit-width allocation using
  SAT-Modulo Theory. In DATE, 2009.
 */
object RangePrecision {

  def doppler(u: Real, v: Real, T: Real): Real = {
    require(-100 <= u && u <= 100 && 20 <= v && v <= 20000 &&
     -30 <= T && T <= 50 && noise(u, 1e-7) && noise(v, 1e-9) && noise(T, 1e-6))

    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))

  } ensuring (res => -138.0 <= res && res <= 0.0 && noise(res, 1e-4))

  
  def doppler0(u: Real, v: Real, T: Real): Real = {
    require(-100 <= u && u <= 100 && 20 <= v && v <= 20000 &&
     -30 <= T && T <= 50 && roundoff(u, v, T))
    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))
  } ensuring (res => -138.0 <= res && res <= 0.0 && noise(res, 1e-4))

  
  def doppler1(u: Real, v: Real, T: Real): Real = {
    require(-100 <= u && u <= 100 && 20 <= v && v <= 20000 &&
     -30 <= T && T <= 50 && roundoff(u, v, T))
    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))
  } ensuring (res => -137.0 <= res && res <= -0.35 && noise(res, 1e-14))

  def doppler2(u: Real, v: Real, T: Real): Real = {
    require(-125 <= u && u <= 125 && 15 <= v && v <= 25000 &&
     -40 <= T && T <= 60 && roundoff(u, v, T))
    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))
  } ensuring (res => -227.5 <= res && res <= -0.05 && noise(res, 1e-12))

  def doppler3(u: Real, v: Real, T: Real): Real = {
    require(-30 <= u && u <= 120 && 320 <= v && v <= 20300 &&
     -50 <= T && T <= 30 && roundoff(u, v, T))
    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))
  } ensuring (res => -82.5 <= res && res <= -0.6 && noise(res, 1e-13))

  def doppler4(u: Real, v: Real, T: Real): Real = {
    require(-125 <= u && u <= 125 && 15 <= v && v <= 25000 &&
     -40 <= T && T <= 60 && noise(u, 1e-7) && noise(v, 1e-9) && noise(T, 1e-6))
    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))
  } ensuring (res => -227.5 <= res && res <= -0.05 && noise(res, 1e-12))

  def doppler5(u: Real, v: Real, T: Real): Real = {
    require(-30 <= u && u <= 120 && 320 <= v && v <= 20300 &&
     -50 <= T && T <= 30 && noise(u, 1e-7) && noise(v, 1e-9) && noise(T, 1e-6))
    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))
  } ensuring (res => -82.5 <= res && res <= -0.6 && noise(res, 1e-13))


  // Sim: [-693.0980449078490,687.4198314598049]    (2.2737367544323206E-13)
  def rigidBody1Invalid(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 15 && x1 >= -15 && x2 <= 15 && x2 >= -15 &&
            x3 <= 15 && x3 >= -15)
    -x1*x2 - 2*x2*x3 - x1 - x3
  } ensuring (res => -694 <= res && res <= 688.0 && noise(res, 1e-12))

  def rigidBody1(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 15 && x1 >= -15 && x2 <= 15 && x2 >= -15 &&
            x3 <= 15 && x3 >= -15)
    -x1*x2 - 2*x2*x3 - x1 - x3
  } ensuring (res => -800 <= res && res <= 750.0 && noise(res, 1e-10))

  // Sim: [-2638.451636347363,2756.816301997386]    (9.094947017729282E-13)
  def rigidBody1_2Invalid(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 13 && x1 >= -20 && x2 <= 25 && x2 >= -25 &&
            x3 <= 35 && x3 >= -45)
    -x1*x2 - 2*x2*x3 - x1 - x3
  } ensuring (res => -2640.0 <= res && res <= 2760.0 && noise(res, 1e-12))

  def rigidBody1_2(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 13 && x1 >= -20 && x2 <= 25 && x2 >= -25 &&
            x3 <= 35 && x3 >= -45)
    -x1*x2 - 2*x2*x3 - x1 - x3
  } ensuring (res => -2850.0 <= res && res <= 2950.0 && noise(res, 1e-9))

  // Sim: [-1142.038583258746,622.6370473435335]    (4.547473508864641E-13)
  def rigidBody1_3(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 20 && x1 >= -10 && x2 <= 10 && x2 >= -20 &&
            x3 <= 5 && x3 >= -25)
    -x1*x2 - 2*x2*x3 - x1 - x3
  } ensuring (res => -1300.0 <= res && res <= 750.0 && noise(res, 1e-9))

  // Sim: [-53914.95897764155,57835.66271360889]    (2.1827872842550278E-11)
  def rigidBody2Invalid(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 15 && x1 >= -15 && x2 <= 15 && x2 >= -15 &&
            x3 <= 15 && x3 >= -15)
    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  } ensuring (res => -53920.0 <= res && res >= 57840.0 && noise(res, 1e-10))
  
  def rigidBody2(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 15 && x1 >= -15 && x2 <= 15 && x2 >= -15 &&
            x3 <= 15 && x3 >= -15)
    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  } ensuring (res => -55500.0 <= res && res >= 59500.0 && noise(res, 1e-8))
   
  // Sim: [-564937.4996816926,471323.6113501612]    (2.3283064365386963E-10)
  def rigidBody2_2Invalid(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 13 && x1 >= -20 && x2 <= 25 && x2 >= -25 &&
            x3 <= 35 && x3 >= -45)
    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  } ensuring (res => -565000.0 <= res && res >= 472000.0 && noise(res, 1e-9))

  def rigidBody2_2(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 13 && x1 >= -20 && x2 <= 25 && x2 >= -25 &&
            x3 <= 35 && x3 >= -45)
    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  } ensuring (res => -650000.0 <= res && res >= 550000.0 && noise(res, 1e-4))

  // Sim: [-100418.7322517922,221185.3529955959]    (8.731149137020111E-11)
  def rigidBody2_3Invalid(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 20 && x1 >= -10 && x2 <= 10 && x2 >= -20 &&
            x3 <= 5 && x3 >= -25)
    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  } ensuring (res => -101000.0 <= res && res >= 222000.0 && noise(res, 1e-10))

  def rigidBody2_3(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 20 && x1 >= -10 && x2 <= 10 && x2 >= -20 &&
            x3 <= 5 && x3 >= -25)
    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  } ensuring (res => -125000.0 <= res && res >= 245000.0 && noise(res, 1e-9))


  // Sim: [-1778.572314073148,4809.339509539625]    (4.547473508864641E-12)
  def jetEngine(x1: Real, x2: Real): Real = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5)
    x1 + ((2*x1*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1))*
    ((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1) - 3) + x1*x1*(4*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  } ensuring (res => -2500.0 <= res && res >= 5500.0 && noise(res, 1e-10))  


   // The input and output bounds are kind of random.

  // Sim: [13.11833645149913,31629066.12856068]    (4.470348358154297E-8)
  def beales(x: Real, y: Real): Real = {
    require(-4 <= x && x <= 0.5 && 1.5 <= y && y <= 4.45)
    (1.5 - x + x*y)*(1.5 - x + x*y) +
    (2.25 - x + x*y*(x*y))*(2.25 - x + x*y*(x*y)) +
    (2.625 - x + x*y*(x*y)*(x*y))*(2.625 - x + x*y*(x*y)*(x*y))
  } ensuring (res => 13.0 <= res && res <= 31629067.0 && noise(res, 1e-7))

  
  //Sim: [14.01916781064652,185495053.2162193]    (2.384185791015625E-7)
  def beales2(x: Real, y: Real): Real = {
    require(-5 <= x && x <= 2.5 && 2.5 <= y && y <= 4.78)
    (1.5 - x + x*y)*(1.5 - x + x*y) +
    (2.25 - x + x*y*(x*y))*(2.25 - x + x*y*(x*y)) +
    (2.625 - x + x*y*(x*y)*(x*y))*(2.625 - x + x*y*(x*y)*(x*y))
  } ensuring (res => 14.0 <= res && res <= 185495100.0 && noise(res, 1e-6))

  // Sim: [0.2860857182376199,64239542.37063869]    (8.940696716308594E-8)
  def beales3(x: Real, y: Real): Real = {
    require(-2 <= x && x <= 4.5 && 0.2 <= y && y <= 4.45)
    (1.5 - x + x*y)*(1.5 - x + x*y) +
    (2.25 - x + x*y*(x*y))*(2.25 - x + x*y*(x*y)) +
    (2.625 - x + x*y*(x*y)*(x*y))*(2.625 - x + x*y*(x*y)*(x*y))
  } ensuring (res => 0.28 <= res && res <= 64239600.0 && noise(res, 1e-7))
  

  // Sim: [180.1158417843523,679.1975462951999]    (3.410605131648481E-13)
  def booths(x: Real, y: Real): Real = {
    require(-9 <= x && x <= -5 && 1 <= y && y <= 3)
    (x + 2*y -7)*(x + 2*y -7) + (2*x + y -5)*(2*x + y -5)
  } ensuring (res => 180.0 <= res && res <= 678.0 && noise(res, 1e-12))

  // Sim: [0.0003442945751460915,1826.126764300354]    (6.821210263296962E-13)
  def booths2(x: Real, y: Real): Real = {
    require(-13 <= x && x <= 2 && -3 <= y && y <= 7.6)
    (x + 2*y -7)*(x + 2*y -7) + (2*x + y -5)*(2*x + y -5)
  } ensuring (res => 0.0 <= res && res <= 1827.0 && noise(res, 1e-12))

  // Sim: [1.802273718141507,784.8745892544846]    (3.410605131648481E-13)
  def booths3(x: Real, y: Real): Real = {
    require(-5 <= x && x <= 6.7 && 4 <= y && y <= 10.5)
    (x + 2*y -7)*(x + 2*y -7) + (2*x + y -5)*(2*x + y -5)
  } ensuring (res => 1.8 <= res && res <= 785.0 && noise(res, 1e-12))
  

  // Sim: [8.493308609645456e-05,2047.524374981617]    (2.2737367544323206E-12)
  def camel(x: Real, y: Real): Real = {
    require(-5 <= x && x <= 5 && -5 <= y && y <= 5)
    2*x*x - 1.05*x*x*x*x + (x*x*x*x*x*x)/6 + x*y + y*y
  } ensuring (res => 0.0 <= res && res <= 2048.0 && noise(res, 1e-11))

  // Sim: [6.728205373144213e-05,1163600.441136090]    (9.313225746154785E-10)
  def camel2(x: Real, y: Real): Real = {
    require(-13.9 <= x && x <= 7.98 && -12.8 <= y && y <= 8.9)
    2*x*x - 1.05*x*x*x*x + (x*x*x*x*x*x)/6 + x*y + y*y
  } ensuring (res => 6.7 <= res && res <= 1163650.0 && noise(res, 1e-8))

  // Sim: [1.335997722024297e-05,143776.6793834211]    (1.4551915228366852E-10)
  def camel3(x: Real, y: Real): Real = {
    require(-2.4 <= x && x <= 9.86 && -1.2 <= y && y <= 14.78)
    2*x*x - 1.05*x*x*x*x + (x*x*x*x*x*x)/6 + x*y + y*y
  } ensuring (res => 1.3 <= res && res <= 143777.0 && noise(res, 1e-8))


  // Sim: [1215.987918907554,351618.8163690719]    (4.0745362639427185E-10)
  // Does not time out!
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

  // Sim: [9.173973378642248,36.33989801853660]    (1.4210854715202004E-14)
  def matyas(x: Real, y: Real): Real  = {
    require(-9 <= x && x <= -5 && 1 <= y && y <= 3)
    0.26*(x*x + y*y) - 0.48*x*y
  } ensuring (res => 9.1 <= res && res <= 36.4 && noise(res, 1e-13))

  // Sim: [1.178824621943839,176.6983532634135]    (5.6843418860808015E-14)
  def matyas2(x: Real, y: Real): Real  = {
    require(-19 <= x && x <= -3 && -1 <= y && y <= 7.5)
    0.26*(x*x + y*y) - 0.48*x*y
  } ensuring (res => 1.1 <= res && res <= 177.0 && noise(res, 1e-13))

  // Sim: [1.502261526737385e-06,70.06356062864200]    (2.8421709430404007E-14)
  def matyas3(x: Real, y: Real): Real  = {
    require(-3.4 <= x && x <= 5 && -11.7 <= y && y <= 1)
    0.26*(x*x + y*y) - 0.48*x*y
  } ensuring (res => 1.5 <= res && res <= 70.1 && noise(res, 1e-13))


  // Sim: [36.21337199193115,486842455.6749934]    (2.384185791015625E-7)
  def motzkin(x: Real, y: Real, z: Real): Real = {
    require(-5.6 <= x && x <= 1.3 && 45.3 <= y && y <= 63.0 &&
            3.2 <= z && z <= 15.7)
    z*z*z + x*x*(y*y) * (z*z + y*y - 3*z*z)
  } ensuring (res => 36.0 <= res && res <= 486842460.0 && noise(res, 1e-6))

  def motzkin2(x: Real, y: Real, z: Real): Real = {
    require(-9.6 <= x && x <= 3.3 && 25.3 <= y && y <= 56.0 &&
            -3.2 <= z && z <= 25.7)
    z*z*z + x*x*(y*y) * (z*z + y*y - 3*z*z)
  } ensuring (res => res >= -56020.0)

  // Sim: [-31.98118558979185,180335165.7024984]    (1.1920928955078125E-7)
  def motzkin3(x: Real, y: Real, z: Real): Real = {
    require(-2.6 <= x && x <= 7.3 && 25.3 <= y && y <= 43.0 &&
            -3.2 <= z && z <= 10.7)
    z*z*z + x*x*(y*y) * (z*z + y*y - 3*z*z)
  } ensuring (res => -32.0 <= res && res <= 180335170.0 && noise(res, 1e-6))
  

  // Sim: [-1.425532517660864,0.9999999999999941]    (1.5543122344752192E-15)
  def cos(x: Real): Real = {
    require(-1.24 <= x && x <= 3.5)
    1 - (x*x)/2.0 + (x*x*x*x)/24.0 - (x*x*x*x*x*x)/720.0
  } ensuring (res => -1.43 <= res && res <= 1.0 && noise(res, 1e-12))

  // sin(x) * cos(x)
  // Sim: [-0.4920575622228202,216.8563439361969]    (1.7053025658242404E-13)
  def cos2(x: Real): Real = {// around 1.34
    require(-3.14 <= x && x <= 3.14)
    0.222687 - 0.895344*(x - 1.34) - 0.445375*(x - 1.34)*(x - 1.34) +
    0.596896*(x - 1.34)*(x - 1.34)*(x - 1.34) +
    0.148458*(x - 1.34)*(x - 1.34)*(x - 1.34)*(x - 1.34) -
    0.119379*(x - 1.34)*(x - 1.34)*(x - 1.34)*(x - 1.34)*(x - 1.34) 
  } ensuring (res => -0.5 <= res && res <= 217.0 && noise(res, 1e-12))

  //cos(sqrt(x + 7.8) *2*x)
  // Sim: [-59.62687322193541,0.9618440785087154]    (3.552713678800501E-14)
  def cos3(x: Real): Real = { //around -3.4
    require(-5.0 <= x && x <= -1.0)
    -0.126295 + 2.55374*(x + 3.4) + 0.982769*(x + 3.4)*(x + 3.4) -
    2.67303*(x + 3.4)*(x + 3.4)*(x + 3.4) -
    2.08817*(x + 3.4)*(x + 3.4)*(x + 3.4)*(x + 3.4) +
    0.438815*(x + 3.4)*(x + 3.4)*(x + 3.4)*(x + 3.4)*(x + 3.4)
  } ensuring (res => -60.0 <= res && res <= 1.0 && noise(res, 1e-12))

  // Sim: [1.000000000000040,5.215020510086066]    (1.7763568394002505E-15)
  def cosh6(x: Real): Real = {
    require(-1.23 <= x && x <= 2.34)
    1 + (x*x)/2.0 + (x*x*x*x)/24.0 + (x*x*x*x*x*x)/720.0
  } ensuring (res => 1.0 <= res && res <= 5.5 && noise(res, 1e-12))
  
  // Sim: [0.6786651176339717,2.986100724817679]    (1.3322676295501878E-15)
  def exOverCosx(x: Real): Real = {
    require(-1.5 <= x && x <= 0.8)
    1 + x + x*x + (2*x*x*x)/3.0 + (x*x*x*x)/2.0
  } ensuring (res => 0.7 <= res && res <= 3.0 && noise(res, 1e-12))

  // Sim: [-0.9756807032849710,0.9579886390597153]    (2.220446049250313E-16)
  def sin(x: Real): Real = {
    require(-1.35 <= x && x <= 1.28)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 - (x*x*x*x*x*x*x)/5040.0
  } ensuring (res => -1.0 <= res && res <= 1.0 && noise(res, 1e-12))

  // sin(1.24*x - 0.087)
  // Sim: [-0.7796391511083967,1.000009916527744]    (1.1102230246251565E-15)
  def sin2(x: Real): Real = {//around 0.98
    require(-1.0 <= x && x <= 2.46)
    0.903643 + 0.531076*(x - 0.98) - 0.694721*(x - 0.98)*(x - 0.98) -
    0.136097*(x - 0.98)*(x - 0.98)*(x - 0.98) +
    0.0890169*(x - 0.98)*(x - 0.98)*(x - 0.98)*(x - 0.98) +
    0.0104631*(x - 0.98)*(x - 0.98)*(x - 0.98)*(x - 0.98)*(x - 0.98)
  } ensuring (res => -0.8 <= res && res <= 1.0 && noise(res, 1e-12))

  // sin(x) * sin(x)
  // Sim: [0.1053730907077877,3.589088717014549]    (5.773159728050814E-15)
  def sin3(x: Real): Real = { // around 1.34
    require(-1.0 <= x && x <= 3.14)
    0.947672 + 0.445375*(x - 1.34) - 0.895344*(x - 1.34)*(x - 1.34) -
    0.296916*(x - 1.34)*(x - 1.34)*(x - 1.34) +
    0.298448*(x - 1.34)*(x - 1.34)*(x - 1.34)*(x - 1.34) +
    0.0593833*(x - 1.34)*(x - 1.34)*(x - 1.34)*(x - 1.34)*(x - 1.34) 
  } ensuring (res => 0.1 <= res && res <= 3.6 && noise(res, 1e-12))
  
  // Sim: [-0.4653298002731128,5.136316766769693]    (2.6645352591003757E-15)
  /*def sinh7(x: Real): Real = {
    require(-0.45 <= x && x <= 2.34)
    x + (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring (res => -0.5 <= res && res <= 5.2 && noise(res) <= 1e-12)
  */

  // Sim: [1.168748495960413,2.068836443423501]    (8.881784197001252E-16)
  // Fails to time out
  def sqrt(x: Real): Real = { // around 3.14
    require(1.35 <= x && x <= 4.28)
    1.772 + 0.282166*(x - 3.14) - 0.0224655*(x - 3.14)*(x - 3.14) +
    0.0035773*(x - 3.14)*(x - 3.14)*(x - 3.14) -
    0.000712043*(x - 3.14)*(x - 3.14)*(x - 3.14)*(x - 3.14) +
    0.000158736*(x - 3.14)*(x - 3.14)*(x - 3.14)*(x - 3.14) 
  } ensuring (res => 1.0 <= res && res <= 2.4 && noise(res, 1e-12))
  

  // 0.0000272113 is not representable as Int/Int
  def sqrt2(x: Real): Real = { // around 7.98
    require(3.35 <= x && x <= 12.28)
    2.82489 + 0.176998*(x- 7.98) - 0.00554505*(x- 7.98)*(x- 7.98) +
    0.000347434*(x- 7.98)*(x- 7.98)*(x- 7.98) -
    0.0000272113*(x- 7.98)*(x- 7.98)*(x- 7.98)*(x- 7.98) 
  } ensuring (res => res <= 1.2)
  

  // sqrt(3*x - 0.3)
  // Sim: [0.2669926110387539,4.520059737484441]    (8.271161533457416E-15)
  def sqrt3(x: Real): Real = { // around 3.2
    require(3.35 <= x && x <= 12.28)
    3.04959 + 0.491869*(x - 3.2) - 0.0396669*(x - 3.2)*(x - 3.2) +
    0.00639788*(x - 3.2)*(x - 3.2)*(x - 3.2) -
    0.0012899*(x - 3.2)*(x - 3.2)*(x - 3.2)*(x - 3.2)
  } ensuring (res => 0.2 <= res && res <= 4.6 && noise(res, 1e-12))

  // Sim: [-2.527343255806877,2.527356134563472]    (8.881784197001252E-16)
  def tan5(x: Real): Real = {
    require(-1.3 <= x && x <= 1.3)
    x + (x*x*x)/3.0 + (2*x*x*x*x*x)/15.0
  } ensuring (res => -2.5 <= res && res <= 2.6 && noise(res, 1e-12))
  
}
