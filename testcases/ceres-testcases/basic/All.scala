

object All {
  


  def bspline0(u: Double): Double = {
    require(0 <= u && u <= 1)
    (1 - u) * (1 - u) * (1 - u) * 0.1666666
  } ensuring (res => -0.05 <= res && res <= 0.17)
  
  def bspline0_2(u: Double): Double = {
    require(-4 <= u && u <= 2)
    (1 - u) * (1 - u) * (1 - u) * 0.1666666
  } ensuring (res => -0.05 <= res && res <= 0.17)
  
  def bspline0_3(u: Double): Double = {
    require(2 <= u && u <= 13)
    (1 - u) * (1 - u) * (1 - u) * 0.1666666
  } ensuring (res => -0.05 <= res && res <= 0.17)



  def bspline1(u: Double): Double = {
    require(0 <= u && u <= 1)
    (3 * u*u*u - 6 * u*u + 4) * 0.1666666
  } ensuring (res => -0.05 <= res && res <= 0.98)
  
  def bspline1_2(u: Double): Double = {
    require(-4 <= u && u <= 2)
    (3 * u*u*u - 6 * u*u + 4) * 0.1666666
  } ensuring (res => -0.05 <= res && res <= 0.98)
  
  def bspline1_3(u: Double): Double = {
    require(2 <= u && u <= 13)
    (3 * u*u*u - 6 * u*u + 4) * 0.1666666
  } ensuring (res => -0.05 <= res && res <= 0.98)



  def bspline2(u: Double): Double = {
    require(0 <= u && u <= 1)
    (-3 * u*u*u  + 3*u*u + 3*u + 1) * 0.1666666
  } ensuring (res => -0.02 <= res && res <= 0.89)
  
  def bspline2_2(u: Double): Double = {
    require(-4 <= u && u <= 2)
    (-3 * u*u*u  + 3*u*u + 3*u + 1) * 0.1666666
  } ensuring (res => -0.02 <= res && res <= 0.89)

  def bspline2_3(u: Double): Double = {
    require(2 <= u && u <= 13)
    (-3 * u*u*u  + 3*u*u + 3*u + 1) * 0.1666666
  } ensuring (res => -0.02 <= res && res <= 0.89)


  def bspline3(u: Double): Double = {
    require(0 <= u && u <= 1)
    u*u*u * 0.1666666
  } ensuring (res => -0.17 <= res && res <= 0.05)

  def bspline3_2(u: Double): Double = {
    require(-4 <= u && u <= 2)
    u*u*u * 0.1666666
  } ensuring (res => -0.17 <= res && res <= 0.05)

  def bspline3_3(u: Double): Double = {
    require(2 <= u && u <= 13)
    u*u*u * 0.1666666
  } ensuring (res => -0.17 <= res && res <= 0.05)

  def rigidBody1(x1: Double, x2: Double, x3: Double): Double = {
    require(x1 <= 15 && x1 >= -15 && x2 <= 15 && x2 >= -15 &&
            x3 <= 15 && x3 >= -15)
    -x1*x2 - 2*x2*x3 - x1 - x3
  } ensuring (res => res <= 705.0)

 def rigidBody1_2(x1: Double, x2: Double, x3: Double): Double = {
    require(x1 <= 13 && x1 >= -20 && x2 <= 25 && x2 >= -25 &&
            x3 <= 35 && x3 >= -45)
    -x1*x2 - 2*x2*x3 - x1 - x3
  } ensuring (res => res <= 705.0)

 def rigidBody1_3(x1: Double, x2: Double, x3: Double): Double = {
    require(x1 <= 20 && x1 >= -10 && x2 <= 10 && x2 >= -20 &&
            x3 <= 5 && x3 >= -25)
    -x1*x2 - 2*x2*x3 - x1 - x3
  } ensuring (res => res <= 705.0)


 
  def rigidBody2(x1: Double, x2: Double, x3: Double): Double = {
    require(x1 <= 15 && x1 >= -15 && x2 <= 15 && x2 >= -15 &&
            x3 <= 15 && x3 >= -15)
    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  } ensuring (res => res >= -32000.0)
  
  def rigidBody2_2(x1: Double, x2: Double, x3: Double): Double = {
    require(x1 <= 13 && x1 >= -20 && x2 <= 25 && x2 >= -25 &&
            x3 <= 35 && x3 >= -45)
    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  } ensuring (res => res >= -32000.0)

  def rigidBody2_3(x1: Double, x2: Double, x3: Double): Double = {
    require(x1 <= 20 && x1 >= -10 && x2 <= 10 && x2 >= -20 &&
            x3 <= 5 && x3 >= -25)
    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  } ensuring (res => res >= -32000.0)



  def jetEngine(x1: Double, x2: Double): Double = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5)
    x1 + ((2*x1*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1))*
    ((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1) - 3) + x1*x1*(4*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  } ensuring (res => res >= -32000.0)


  def doppler(u: Double, v: Double, T: Double): Double = {
    require(-100 <= u && u <= 100 && 20 <= v && v <= 20000 &&
     -30 <= T && T <= 50)
    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))
  } ensuring (res => 0.0 <= res && res <= 138.0)
  
  // TODO: making the bounds here larger produces a division-by-zero
  //larger bounds
  def doppler2(u: Double, v: Double, T: Double): Double = {
    require(-125 <= u && u <= 125 && 15 <= v && v <= 25000 &&
     -40 <= T && T <= 60)
    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))
  } ensuring (res => 0.0 <= res && res <= 138.0)

  // shifted bounds
  def doppler3(u: Double, v: Double, T: Double): Double = {
    require(-30 <= u && u <= 120 && 320 <= v && v <= 20300 &&
     -50 <= T && T <= 30)
    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))
  } ensuring (res => 0.0 <= res && res <= 138.0)


  def beales(x: Double, y: Double): Double = {
    require(-4 <= x && x <= 0.5 && 1.5 <= y && y <= 4.45)
    (1.5 - x + x*y)*(1.5 - x + x*y) +
    (2.25 - x + x*y*(x*y))*(2.25 - x + x*y*(x*y)) +
    (2.625 - x + x*y*(x*y)*(x*y))*(2.625 - x + x*y*(x*y)*(x*y))
  } ensuring (res => res >= -56020.0)

  def beales2(x: Double, y: Double): Double = {
    require(-5 <= x && x <= 2.5 && 2.5 <= y && y <= 4.78)
    (1.5 - x + x*y)*(1.5 - x + x*y) +
    (2.25 - x + x*y*(x*y))*(2.25 - x + x*y*(x*y)) +
    (2.625 - x + x*y*(x*y)*(x*y))*(2.625 - x + x*y*(x*y)*(x*y))
  } ensuring (res => res >= -56020.0)
 
  def beales3(x: Double, y: Double): Double = {
    require(-2 <= x && x <= 4.5 && 0.2 <= y && y <= 4.45)
    (1.5 - x + x*y)*(1.5 - x + x*y) +
    (2.25 - x + x*y*(x*y))*(2.25 - x + x*y*(x*y)) +
    (2.625 - x + x*y*(x*y)*(x*y))*(2.625 - x + x*y*(x*y)*(x*y))
  } ensuring (res => res >= -56020.0)
 


  def booths(x: Double, y: Double): Double = {
    require(-9 <= x && x <= -5 && 1 <= y && y <= 3)
    (x + 2*y -7)*(x + 2*y -7) + (2*x + y -5)*(2*x + y -5)
  } ensuring (res => res >= -56020.0)

  def booths2(x: Double, y: Double): Double = {
    require(-13 <= x && x <= 2 && -3 <= y && y <= 7.6)
    (x + 2*y -7)*(x + 2*y -7) + (2*x + y -5)*(2*x + y -5)
  } ensuring (res => res >= -56020.0)
  
  def booths3(x: Double, y: Double): Double = {
    require(-5 <= x && x <= 6.7 && 4 <= y && y <= 10.5)
    (x + 2*y -7)*(x + 2*y -7) + (2*x + y -5)*(2*x + y -5)
  } ensuring (res => res >= -56020.0)



  def camel(x: Double, y: Double): Double = {
    require(-5 <= x && x <= 5 && -5 <= y && y <= 5)
    2*x*x - 1.05*x*x*x*x + (x*x*x*x*x*x)/6 + x*y + y*y
  } ensuring (res => res >= -56020.0)

  def camel2(x: Double, y: Double): Double = {
    require(-13.9 <= x && x <= 7.98 && -12.8 <= y && y <= 8.9)
    2*x*x - 1.05*x*x*x*x + (x*x*x*x*x*x)/6 + x*y + y*y
  } ensuring (res => res >= -56020.0)
  
  def camel3(x: Double, y: Double): Double = {
    require(-2.4 <= x && x <= 9.86 && -1.2 <= y && y <= 14.78)
    2*x*x - 1.05*x*x*x*x + (x*x*x*x*x*x)/6 + x*y + y*y
  } ensuring (res => res >= -56020.0)



  def goldstein(x: Double, y: Double): Double = {
    require(-1.5 <= x && x <= 0.5 && 0.5 <= y && y <= 1.5)
    (1 + (x + y + 1)*(x + y + 1) *(19 - 14*x + 3*x*x - 14*y + 6*x*y + 3*y*y)) *
    (30 + (2*x - 3*y)*(2*x - 3*y) * (18 - 32*x + 12*x*x +48*y - 36*x*y + 27*y*y))
  } ensuring (res => res >= -56020.0)
  

  def matyas(x: Double, y: Double): Double  = {
    require(-9 <= x && x <= -5 && 1 <= y && y <= 3)
    0.26*(x*x + y*y) - 0.48*x*y
  } ensuring (res => res >= -56020.0)

  def matyas2(x: Double, y: Double): Double  = {
    require(-19 <= x && x <= -3 && -1 <= y && y <= 7.5)
    0.26*(x*x + y*y) - 0.48*x*y
  } ensuring (res => res >= -56020.0)
  
  def matyas3(x: Double, y: Double): Double  = {
    require(-3.4 <= x && x <= 5 && -11.7 <= y && y <= 1)
    0.26*(x*x + y*y) - 0.48*x*y
  } ensuring (res => res >= -56020.0)
  


  def motzkin(x: Double, y: Double, z: Double): Double = {
    require(-5.6 <= x && x <= 1.3 && 45.3 <= y && y <= 63.0 &&
            3.2 <= z && z <= 15.7)
    z*z*z + x*x*(y*y) * (z*z + y*y - 3*z*z)
  } ensuring (res => res >= -56020.0)
 
  def motzkin3(x: Double, y: Double, z: Double): Double = {
    require(-2.6 <= x && x <= 7.3 && 25.3 <= y && y <= 43.0 &&
            -3.2 <= z && z <= 10.7)
    z*z*z + x*x*(y*y) * (z*z + y*y - 3*z*z)
  } ensuring (res => res >= -56020.0)

    
  def cos(x: Double): Double = {
    require(-1.24 <= x && x <= 3.5)
    1 - (x*x)/2.0 + (x*x*x*x)/24.0 - (x*x*x*x*x*x)/720.0
  } ensuring (res => res <= 1.2)

  // sin(x) * cos(x)
  def cos2(x: Double): Double = {// around 1.34
    require(-3.14 <= x && x <= 3.14)
    0.222687 - 0.895344*(x - 1.34) - 0.445375*(x - 1.34)*(x - 1.34) +
    0.596896*(x - 1.34)*(x - 1.34)*(x - 1.34) +
    0.148458*(x - 1.34)*(x - 1.34)*(x - 1.34)*(x - 1.34) -
    0.119379*(x - 1.34)*(x - 1.34)*(x - 1.34)*(x - 1.34)*(x - 1.34) 
  } ensuring (res => res <= 1.2)

  //cos(sqrt(x + 7.8) *2*x)
  def cos3(x: Double): Double = { //around -3.4
    require(-5.0 <= x && x <= -1.0)
    -0.126295 + 2.55374*(x + 3.4) + 0.982769*(x + 3.4)*(x + 3.4) -
    2.67303*(x + 3.4)*(x + 3.4)*(x + 3.4) -
    2.08817*(x + 3.4)*(x + 3.4)*(x + 3.4)*(x + 3.4) +
    0.438815*(x + 3.4)*(x + 3.4)*(x + 3.4)*(x + 3.4)*(x + 3.4)
  } ensuring (res => res <= 1.2)

  def cosh6(x: Double): Double = {
    require(-1.23 <= x && x <= 2.34)
    1 + (x*x)/2.0 + (x*x*x*x)/24.0 + (x*x*x*x*x*x)/720.0
  } ensuring (res => res <= 1.2)

  def exOverCosx(x: Double): Double = {
    require(-1.5 <= x && x <= 0.8)
    1 + x + x*x + (2*x*x*x)/3.0 + (x*x*x*x)/2.0
  } ensuring (res => res <= 5.0)

 
  def sin(x: Double): Double = {
    require(-1.35 <= x && x <= 1.28)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 - (x*x*x*x*x*x*x)/5040.0
  } ensuring (res => res <= 1.2)

  // sin(1.24*x - 0.087)
  def sin2(x: Double): Double = {//around 0.98
    require(-1.0 <= x && x <= 2.46)
    0.903643 + 0.531076*(x - 0.98) - 0.694721*(x - 0.98)*(x - 0.98) -
    0.136097*(x - 0.98)*(x - 0.98)*(x - 0.98) +
    0.0890169*(x - 0.98)*(x - 0.98)*(x - 0.98)*(x - 0.98) +
    0.0104631*(x - 0.98)*(x - 0.98)*(x - 0.98)*(x - 0.98)*(x - 0.98)
  } ensuring (res => res <= 1.2)

  // sin(x) * sin(x)
  def sin3(x: Double): Double = { // around 1.34
    require(-1.0 <= x && x <= 3.14)
    0.947672 + 0.445375*(x - 1.34) - 0.895344*(x - 1.34)*(x - 1.34) -
    0.296916*(x - 1.34)*(x - 1.34)*(x - 1.34) +
    0.298448*(x - 1.34)*(x - 1.34)*(x - 1.34)*(x - 1.34) +
    0.0593833*(x - 1.34)*(x - 1.34)*(x - 1.34)*(x - 1.34)*(x - 1.34) 
  } ensuring (res => res <= 1.2)

  def sinh7(x: Double): Double = {
    require(-0.45 <= x && x <= 2.34)
    x + (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring (res => res <= 1.2)





  def sqrt(x: Double): Double = { // around 3.14
    require(1.35 <= x && x <= 4.28)
    1.772 + 0.282166*(x - 3.14) - 0.0224655*(x - 3.14)*(x - 3.14) +
    0.0035773*(x - 3.14)*(x - 3.14)*(x - 3.14) -
    0.000712043*(x - 3.14)*(x - 3.14)*(x - 3.14)*(x - 3.14) +
    0.000158736*(x - 3.14)*(x - 3.14)*(x - 3.14)*(x - 3.14) 
  } ensuring (res => res <= 1.2)

  def sqrt2(x: Double): Double = { // around 7.98
    require(3.35 <= x && x <= 12.28)
    2.82489 + 0.176998*(x- 7.98) - 0.00554505*(x- 7.98)*(x- 7.98) +
    0.000347434*(x- 7.98)*(x- 7.98)*(x- 7.98) -
    0.0000272113*(x- 7.98)*(x- 7.98)*(x- 7.98)*(x- 7.98) 
  } ensuring (res => res <= 1.2)
  

  // sqrt(3*x - 0.3)
  def sqrt3(x: Double): Double = { // around 3.2
    require(3.35 <= x && x <= 12.28)
    3.04959 + 0.491869*(x - 3.2) - 0.0396669*(x - 3.2)*(x - 3.2) +
    0.00639788*(x - 3.2)*(x - 3.2)*(x - 3.2) -
    0.0012899*(x - 3.2)*(x - 3.2)*(x - 3.2)*(x - 3.2)
  } ensuring (res => res <= 1.2)


  def tan5(x: Double): Double = {
    require(-1.3 <= x && x <= 1.3)
    x + (x*x*x)/3.0 + (2*x*x*x*x*x)/15.0
  } ensuring (res => res <= 3.7)



}
