import leon.real._
import RealOps._


object ValBenchmarksStraight {


  def doppler1(u: Real, v: Real, T: Real): Real = {
    require(-100.0 <= u && u <= 100 && 20 <= v && v <= 20000 && -30 <= T && T <= 50)
    (- (331.4 + 0.6 * T) *v) / (((331.4 + 0.6 * T) + u)*((331.4 + 0.6 * T) + u))
  } ensuring(res => res +/- 1e-12)


  def rigidBody1(x1: Real, x2: Real, x3: Real): Real = {
    require(-15.0 <= x1 && x1 <= 15 && -15.0 <= x2 && x2 <= 15.0 && -15.0 <= x3 && x3 <= 15)

    (-x1*x2 - 2*x2*x3) - x1 - x3
  }

  def rigidBody1_2(x1: Real, x2: Real, x3: Real): Real = {
    require(-15.0 <= x1 && x1 <= 15 && -15.0 <= x2 && x2 <= 15.0 && -15.0 <= x3 && x3 <= 15 &&
      x1 +/- 1e-8 && x2 +/- 1e-8 && x3 +/- 1e-8)

    (-x1*x2 - 2*x2*x3) - x1 - x3
  }

  def rigidBody2(x1: Real, x2: Real, x3: Real): Real = {
    require(-15.0 <= x1 && x1 <= 15 && -15.0 <= x2 && x2 <= 15.0 && -15.0 <= x3 && x3 <= 15)

    2*(x1*x2*x3) + (3*x3*x3) - x2*(x1*x2*x3) + (3*x3*x3) - x2
  }

  def rigidBody2_2(x1: Real, x2: Real, x3: Real): Real = {
    require(-15.0 <= x1 && x1 <= 15 && -15.0 <= x2 && x2 <= 15.0 && -15.0 <= x3 && x3 <= 15 &&
      x1 +/- 1e-8 && x2 +/- 1e-8 && x3 +/- 1e-8)

    2*(x1*x2*x3) + (3*x3*x3) - x2*(x1*x2*x3) + (3*x3*x3) - x2
  }

  def jetEngine1(x1: Real, x2: Real): Real = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5)

    x1 + ((2*x1*(((3*x1*x1 + 2*x2 - x1))/(x1*x1 + 1))*
    (((3*x1*x1 + 2*x2 - x1))/(x1*x1 + 1) - 3) + x1*x1*(4*(((3*x1*x1 + 2*x2 - x1))/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(((3*x1*x1 + 2*x2 - x1))/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  }


  def jetEngine1_2(x1: Real, x2: Real): Real = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5 &&
      x1 +/- 1e-8 && x2 +/- 1e-8)

    x1 + ((2*x1*(((3*x1*x1 + 2*x2 - x1))/(x1*x1 + 1))*
    (((3*x1*x1 + 2*x2 - x1))/(x1*x1 + 1) - 3) + x1*x1*(4*(((3*x1*x1 + 2*x2 - x1))/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(((3*x1*x1 + 2*x2 - x1))/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  }

  def turbine1(v: Real, w: Real, r: Real): (Real, Real, Real) = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8)

    val r1 = 3 + 2/(r*r) - 0.125*(3-2*v)*(w*w*r*r)/(1-v) - 4.5
    val r2 = 6*v - 0.5 * v * (w*w*r*r) / (1-v) - 2.5
    val r3 = 3 - 2/(r*r) - 0.125 * (1+2*v) * (w*w*r*r) / (1-v) - 0.5
    (r1, r2, r3)
  }

  def turbine2(v: Real, w: Real, r: Real): (Real, Real, Real) = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8 && 
      v +/- 1e-7 && w +/- 1e-12 && r +/- 1e-8)

    val r1 = 3 + 2/(r*r) - 0.125*(3-2*v)*(w*w*r*r)/(1-v) - 4.5
    val r2 = 6*v - 0.5 * v * (w*w*r*r) / (1-v) - 2.5
    val r3 = 3 - 2/(r*r) - 0.125 * (1+2*v) * (w*w*r*r) / (1-v) - 0.5
    (r1, r2, r3)
  }

  def predatorPrey(r: Real, K: Real, x: Real): Real = {
    require(r >= 4.0 && r <= 4.0 && K >= 1.11 && K <= 1.11 && 0.1 <= x && x <= 0.3)

    (r*x*x) / (1 + (x/K)*(x/K))

  }

  def predatorPrey2(r: Real, K: Real, x: Real): Real = {
    require(r >= 4.0 && r <= 4.0 && K >= 1.11 && K <= 1.11 && 0.1 <= x && x <= 0.3 &&
      r +/- 0.001 && K +/- 1e-5 && x +/- 1e-6)

    (r*x*x) / (1 + (x/K)*(x/K))

  }

}