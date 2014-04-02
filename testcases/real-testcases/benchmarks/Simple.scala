import leon.Real
import Real._


object Simple {

  def doppler1Star(u: Real, v: Real, T: Real): Real = {
    require(-100.0 < u && u < 100 && 20 < v && v < 20000 && -30 < T && T < 50 &&
      u +/- 1e-7 && v +/- 1e-9 && T +/- 1e-6)
    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))
  } ensuring(res => -137.63858 < res && res < -0.03394 && res +/- 2.3548e-6)

  def doppler1(u: Real, v: Real, T: Real): Real = {
    require(-100.0 <= u && u <= 100 && 20 <= v && v <= 20000 && -30 <= T && T <= 50)
    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))
  } ensuring(res => -137.63858 < res && res < -0.03394 && res +/- 4.91906e-13)

  def doppler2Star(u: Real, v: Real, T: Real): Real = {
    require(-125.0 <= u && u <= 125.0 && 15.0 <= v && v <= 25000 && -40 <= T && T <= 60 &&
      u +/- 1e-12 && v +/- 1e-3 && T +/- 1e-5)
    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))
  } ensuring(res => -230.990546 < res && res < -0.0227296 && res +/- 6.201847e-5)

  def doppler2(u: Real, v: Real, T: Real): Real = {
    require(-125.0 <= u && u <= 125.0 && 15.0 <= v && v <= 25000 && -40 <= T && T <= 60)
    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))
  } ensuring(res => -230.990546 < res && res < -0.0227296 && res +/- 1.285034e-12)

  def doppler3Star(u: Real, v: Real, T: Real): Real = {
    require(-30 <= u && u <= 120 && 320.0 <= v && v <= 20300 && -50 <= T && T <= 30 &&
      u +/- 1e-4 && v +/- 1e-5 && T +/- 1e-9)
    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))
  } ensuring(res => -83.0653 < res && res < -0.507441 && res +/- 0.0001228)

  def doppler3(u: Real, v: Real, T: Real): Real = {
    require(-30 <= u && u <= 120 && 320.0 <= v && v <= 20300 && -50 <= T && T <= 30)
    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))
  } ensuring(res => -83.06530 < res && res < -0.507441 && res +/- 2.027446e-13)



  def rigidBody1Star(x1: Real, x2: Real, x3: Real): Real = {
    require(-15.0 <= x1 && x1 <= 15 && -15.0 <= x2 && x2 <= 15.0 && -15.0 <= x3 && x3 <= 15 &&
      x1 +/- 1e-8 && x2 +/- 1e-8 && x3 +/- 1e-8)
    -x1*x2 - 2*x2*x3 - x1 - x3
  } ensuring(res => -705.0 <= res && res <= 705.0 && res +/- 9.20001e-7)

  def rigidBody1(x1: Real, x2: Real, x3: Real): Real = {
    require(-15.0 <= x1 && x1 <= 15 && -15.0 <= x2 && x2 <= 15.0 && -15.0 <= x3 && x3 <= 15)

    -x1*x2 - 2*x2*x3 - x1 - x3
  } ensuring(res => -705.0 <= res && res <= 705.0 && res +/- 5.079271e-13)

  def rigidBody2Star(x1: Real, x2: Real, x3: Real): Real = {
    require(-15.0 <= x1 && x1 <= 15 && -15.0 <= x2 && x2 <= 15.0 && -15.0 <= x3 && x3 <= 15 &&
      x1 +/- 1e-8 && x2 +/- 1e-8 && x3 +/- 1e-8)

    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  } ensuring(res => -56010.0001 <= res && res <= 58740.0 && res +/- 0.0001504)

  def rigidBody2(x1: Real, x2: Real, x3: Real): Real = {
    require(-15.0 <= x1 && x1 <= 15 && -15.0 <= x2 && x2 <= 15.0 && -15.0 <= x3 && x3 <= 15)

    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  } ensuring(res => -56010.0001 <= res && res <= 58740.0 && res +/- 6.475184e-11)


  /*def jetEngineStar(x1: Real, x2: Real): Real = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5 && x1 +/- 1e-8 && x2 +/- 1e-8)

    val t = (3*x1*x1 + 2*x2 - x1)

    x1 + ((2*x1*(t/(x1*x1 + 1))*
    (t/(x1*x1 + 1) - 3) + x1*x1*(4*(t/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(t/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  } ensuring(res => res +/- 0.1400174)

  def jetEngine(x1: Real, x2: Real): Real = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5)

    val t = (3*x1*x1 + 2*x2 - x1)

    x1 + ((2*x1*(t/(x1*x1 + 1))*
    (t/(x1*x1 + 1) - 3) + x1*x1*(4*(t/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(t/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  } ensuring(res => -1997.0368 < res && res < 5109.33738 && res +/- 1.6170399e-8)
  */

  def turbine1Star(v: Real, w: Real, r: Real): Real = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8 &&
      v +/- 1e-7 && w +/- 1e-12 && r +/- 1e-8)

    3 + 2/(r*r) - 0.125*(3-2*v)*(w*w*r*r)/(1-v) - 4.5
  } ensuring(res => -18.525727 < res && res < -1.991604 && res +/- 4.855807e-6)

  def turbine1(v: Real, w: Real, r: Real): Real = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8)

    3 + 2/(r*r) - 0.125*(3-2*v)*(w*w*r*r)/(1-v) - 4.5
  } ensuring(res => -18.525727 < res && res < -1.991604 && res +/- 1.24162e-13)

  def turbine2Star(v: Real, w: Real, r: Real): Real = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8 &&
      v +/- 1e-7 && w +/- 1e-12 && r +/- 1e-8)

    6*v - 0.5 * v * (w*w*r*r) / (1-v) - 2.5
  } ensuring(res => -28.55484 < res && res < 3.822207 && res +/- 8.04866e-6)

  def turbine2(v: Real, w: Real, r: Real): Real = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8)

    6*v - 0.5 * v * (w*w*r*r) / (1-v) - 2.5
  } ensuring(res => -28.55484 < res && res < 3.822207 && res +/- 1.757041e-13)

  def turbine3Star(v: Real, w: Real, r: Real): Real = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8 &&
      v +/- 1e-7 && w +/- 1e-12 && r +/- 1e-8)

    3 - 2/(r*r) - 0.125 * (1+2*v) * (w*w*r*r) / (1-v) - 0.5
  } ensuring(res => 0.571726 < res && res < 11.4272 && res +/- 3.349164e-6)

  def turbine3(v: Real, w: Real, r: Real): Real = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8)

    3 - 2/(r*r) - 0.125 * (1+2*v) * (w*w*r*r) / (1-v) - 0.5
  } ensuring(res => 0.571726 < res && res < 11.4272 && res +/- 8.49926e-14)



  def verhulstStar(r: Real, K: Real, x: Real): Real = {
    require(r >= 4.0 && r <= 4.0 && K >= 1.11 && K <= 1.11 && 0.1 <= x && x <= 0.3 &&
      r +/- 0.001 && K +/- 1e-5 && x +/- 1e-6)

    (r*x) / (1 + (x/K))

  } ensuring(res => 0.3148936 < res && res < 1.1008265 && res +/- 0.0002811)

  def verhulst(r: Real, K: Real, x: Real): Real = {
    require(r >= 4.0 && r <= 4.0 && K >= 1.11 && K <= 1.11 && 0.1 <= x && x <= 0.3)

    (r*x) / (1 + (x/K))

  } ensuring(res => 0.3148936 < res && res < 1.1008265 && res +/- 6.817851e-16)

  /*def predatorPreyStar(r: Real, K: Real, x: Real): Real = {
    require(r >= 4.0 && r <= 4.0 && K >= 1.11 && K <= 1.11 && 0.1 <= x && x <= 0.3 &&
      r +/- 0.001 && K +/- 1e-5 && x +/- 1e-6)

    (r*x*x) / (1 + (x/K)*(x/K))

  } ensuring(res => 0.039677 <= res && res <= 0.335495 && res +/- 9.2168e-4)
  */
  def predatorPrey(r: Real, K: Real, x: Real): Real = {
    require(r >= 4.0 && r <= 4.0 && K >= 1.11 && K <= 1.11 && 0.1 <= x && x <= 0.3)

    (r*x*x) / (1 + (x/K)*(x/K))

  } ensuring(res => 0.0396779 < res && res < 0.335494 && res +/- 2.9353124e-16)



  def carbonGasStar(T: Real, a: Real, b: Real, N: Real, p: Real, V: Real): Real = {
    require(T >= 300 && T <= 300 && a >= 0.401 && a <= 0.401 && b >= 42.7e-6 && b <= 42.7e-6 && N >= 1000 && N <= 1000 &&
    p >= 3.5e7 && p <= 3.5e7 && 0.1 <= V && V <= 0.5 && T +/- 0.01 && a +/- 1e-6 && b +/- 1e-10 && N +/- 5 && p +/- 1e-13 && V +/- 0.005)

    val k = 1.3806503e-23
    (p + a * (N / V) * (N / V)) * (V - N * b) - k * N * T

  } ensuring(res => 4303229.99 < res && res <= 16739009.21 && res +/- 2114297.83596)

  def carbonGas(T: Real, a: Real, b: Real, N: Real, p: Real, V: Real): Real = {
    require(T >= 300 && T <= 300 && a >= 0.401 && a <= 0.401 && b >= 42.7e-6 && b <= 42.7e-6 && N >= 1000 && N <= 1000 &&
    p >= 3.5e7 && p <= 3.5e7 && 0.1 <= V && V <= 0.5)

    val k = 1.3806503e-23
    (p + a * (N / V) * (N / V)) * (V - N * b) - k * N * T

  } ensuring(res => 4303229.99 < res && res <= 16739009.21 && res +/- 4.63471061e-8)



  def sine(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 - (x*x*x*x*x*x*x)/5040.0 
  } ensuring(res => -0.9998435 < res && res < 0.9998435 && res +/- 9.55412e-16)

  def sqroot(x: Real): Real = {
    require(x >= 0.0 && x < 1.0)
    1.0 + 0.5*x - 0.125*x*x + 0.0625*x*x*x - 0.0390625*x*x*x*x
  } ensuring(res => 0.9999999 < res && res < 1.398438 && res +/- 8.4047353e-16)

  def sineOrder3(x: Real): Real = {
    require(-2.0 < x && x < 2.0)
    0.954929658551372 * x -  0.12900613773279798*(x*x*x)
  } ensuring(res => -1.00000001 < res && res < 1.0000001 && res +/- 1.1079986e-15)

}