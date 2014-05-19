import leon.real._
import RealOps._


object ValBenchmarks {


  def doppler1(u: Real, v: Real, T: Real): Real = {
    require(-100.0 <= u && u <= 100 && 20 <= v && v <= 20000 && -30 <= T && T <= 50)
    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))
  } ensuring(res => -137.63858 < res && res < -0.03394 && res +/- 4.91906e-13)


  def rigidBody1(x1: Real, x2: Real, x3: Real): Real = {
    require(-15.0 <= x1 && x1 <= 15 && -15.0 <= x2 && x2 <= 15.0 && -15.0 <= x3 && x3 <= 15)

    val t = -x1*x2 - 2*x2*x3 
    t - x1 - x3
  } ensuring(res => -705.0 <= res && res <= 705.0 && res +/- 5.079271e-13)

  def rigidBody1_2(x1: Real, x2: Real, x3: Real): Real = {
    require(-15.0 <= x1 && x1 <= 15 && -15.0 <= x2 && x2 <= 15.0 && -15.0 <= x3 && x3 <= 15 &&
      x1 +/- 1e-8 && x2 +/- 1e-8 && x3 +/- 1e-8)

    val t = -x1*x2 - 2*x2*x3 
    t - x1 - x3
  } ensuring(res => -705.0 <= res && res <= 705.0 && res +/- 9.20001e-7)

  def rigidBody2(x1: Real, x2: Real, x3: Real): Real = {
    require(-15.0 <= x1 && x1 <= 15 && -15.0 <= x2 && x2 <= 15.0 && -15.0 <= x3 && x3 <= 15)

    val t = x1*x2*x3
    val t2 = 3*x3*x3

    2*t + t2 - x2*t + t2 - x2
  } ensuring(res => -56010.0001 <= res && res <= 58740.0 && res +/- 6.475184e-11)

  def rigidBody2_2(x1: Real, x2: Real, x3: Real): Real = {
    require(-15.0 <= x1 && x1 <= 15 && -15.0 <= x2 && x2 <= 15.0 && -15.0 <= x3 && x3 <= 15 &&
      x1 +/- 1e-8 && x2 +/- 1e-8 && x3 +/- 1e-8)

    val t = x1*x2*x3
    val t2 = 3*x3*x3

    2*t + t2 - x2*t + t2 - x2
  } ensuring(res => -56010.0001 <= res && res <= 58740.0 && res +/- 0.0001504)

  def jetEngine1(x1: Real, x2: Real): Real = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5)

    val t = (3*x1*x1 + 2*x2 - x1)

    x1 + ((2*x1*(t/(x1*x1 + 1))*
    (t/(x1*x1 + 1) - 3) + x1*x1*(4*(t/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(t/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  }

  def jetEngine2(x1: Real, x2: Real): Real = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5)

    val t = (3*x1*x1 + 2*x2 - x1)
    val t2 = x1*x1 + 1

    x1 + ((2*x1*(t/t2)*
    (t/t2 - 3) + x1*x1*(4*(t/t2)-6))*
    t2 + 3*x1*x1*(t/t2) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/t2))
  }

  def jetEngine1_2(x1: Real, x2: Real): Real = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5 &&
      x1 +/- 1e-8 && x2 +/- 1e-8)

    val t = (3*x1*x1 + 2*x2 - x1)

    x1 + ((2*x1*(t/(x1*x1 + 1))*
    (t/(x1*x1 + 1) - 3) + x1*x1*(4*(t/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(t/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  }

  def jetEngine2_2(x1: Real, x2: Real): Real = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5 &&
      x1 +/- 1e-8 && x2 +/- 1e-8)

    val t = (3*x1*x1 + 2*x2 - x1)
    val t2 = x1*x1 + 1

    x1 + ((2*x1*(t/t2)*
    (t/t2 - 3) + x1*x1*(4*(t/t2)-6))*
    t2 + 3*x1*x1*(t/t2) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/t2))
  }

  def turbine1(v: Real, w: Real, r: Real): (Real, Real, Real) = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8)

    val t1 = w*w*r*r

    val r1 = 3 + 2/(r*r) - 0.125*(3-2*v)*t1/(1-v) - 4.5
    val r2 = 6*v - 0.5 * v * t1 / (1-v) - 2.5
    val r3 = 3 - 2/(r*r) - 0.125 * (1+2*v) * t1 / (1-v) - 0.5
    (r1, r2, r3)
  } ensuring(_ match {
    case (a, b, c) => -18.525727 < a && a < -1.991604 && a +/- 1.24162e-13 &&
      -28.55484 < b && b < 3.822207 && b +/- 1.757041e-13 &&
       0.571726 < c && c < 11.4272 && c +/- 8.49926e-14
    })

  /*def turbine1_2(v: Real, w: Real, r: Real): (Real, Real, Real) = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8)

    val t1 = w*w*r*r

    val t2 = - 0.125*(3-2*v)*t1/(1-v) - 4.5
    val t3 = - 0.5 * v * t1 / (1-v)
    val t4 = 0.125 * (1+2*v) * t1 / (1-v)

    val r1 = 3 + 2/(r*r) + t2
    val r2 = 6*v + t3 - 2.5
    val r3 = 3 - 2/(r*r) - t4 - 0.5
    (r1, r2, r3)
  }*/

  def turbine2(v: Real, w: Real, r: Real): (Real, Real, Real) = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8 && 
      v +/- 1e-7 && w +/- 1e-12 && r +/- 1e-8)

    val t1 = w*w*r*r

    val r1 = 3 + 2/(r*r) - 0.125*(3-2*v)*t1/(1-v) - 4.5
    val r2 = 6*v - 0.5 * v * t1 / (1-v) - 2.5
    val r3 = 3 - 2/(r*r) - 0.125 * (1+2*v) * t1 / (1-v) - 0.5
    (r1, r2, r3)
  } ensuring(_ match {
    case (a, b, c) => -18.525727 < a && a < -1.991604 && a +/- 4.855807e-6 &&
      -28.55484 < b && b < 3.822207 && b +/- 8.04866e-6 &&
       0.571726 < c && c < 11.4272 && c +/- 3.349164e-6
    })

  def predatorPrey(r: Real, K: Real, x: Real): Real = {
    require(r >= 4.0 && r <= 4.0 && K >= 1.11 && K <= 1.11 && 0.1 <= x && x <= 0.3)

    val t = (1 + (x/K)*(x/K))
    (r*x*x) / t

  } ensuring(res => 0.0396779 < res && res < 0.335494 && res +/- 2.9353124e-16)

  def predatorPrey2(r: Real, K: Real, x: Real): Real = {
    require(r >= 4.0 && r <= 4.0 && K >= 1.11 && K <= 1.11 && 0.1 <= x && x <= 0.3 &&
      r +/- 0.001 && K +/- 1e-5 && x +/- 1e-6)

    val t = (1 + (x/K)*(x/K))
    (r*x*x) / t

  } ensuring(res => 0.039677 <= res && res <= 0.335495 && res +/- 9.2168e-4)

}