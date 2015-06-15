import leon.real._
import RealOps._


object StraightlineWithConstraints {

  def dopplerRefConstr(u: Real, v: Real, T: Real): Real = {
    require(-100.0 <= u && u <= 100 && 20 <= v && v <= 20000 && -30 <= T && T <= 50 &&
      u*u + v*v + T*T <= 201000)

    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))

  }

  def dopplerRefErrConstr(u: Real, v: Real, T: Real): Real = {
    require(-100.0 <= u && u <= 100 && 20 <= v && v <= 20000 && -30 <= T && T <= 50 &&
      u*u + v*v + T*T <= 201000 && u +/- 1e-11 && v +/- 1e-11 && T +/- 1e-11)

    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))

  }

  /*def rigidBody1(x1: Real, x2: Real, x3: Real): Real = {
    require(-15.0 <= x1 && x1 <= 15 && -15.0 <= x2 && x2 <= 15.0 && -15.0 <= x3 && x3 <= 15)

    -x1*x2 - 2*x2*x3 - x1 - x3
  }*/

  def rigidBody2RefConstr(x1: Real, x2: Real, x3: Real): Real = {
    require(-15.0 <= x1 && x1 <= 15 && -15.0 <= x2 && x2 <= 15.0 &&
      -15.0 <= x3 && x3 <= 15 && x1*x1 + x2*x2 + x3*x3 <= 300.0)

    val t1 = x1*x2*x3
    val t2 = 3*x3*x3
    2*(t1) + (t2) - x2*(t1) + (t2) - x2
  }


  def rigidBody2RefErrConstr(x1: Real, x2: Real, x3: Real): Real = {
    require(-15.0 <= x1 && x1 <= 15 && -15.0 <= x2 && x2 <= 15.0 &&
      -15.0 <= x3 && x3 <= 15 && x1*x1 + x2*x2 + x3*x3 <= 300.0 &&
      x1 +/- 1e-11 && x2 +/- 1e-11 && x3 +/- 1e-11)

    val t1 = x1*x2*x3
    val t2 = 3*x3*x3
    2*(t1) + (t2) - x2*(t1) + (t2) - x2
  }

  def jetEngineRefConstr(x1: Real, x2: Real): Real = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5 &&
      x1*x1 + x2*x2 <= 404.0)

    val t = (3*x1*x1 + 2*x2 - x1)

    x1 + ((2*x1*(t/(x1*x1 + 1))*
    (t/(x1*x1 + 1) - 3) + x1*x1*(4*(t/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(t/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1)))
  }

  def jetEngineRefErrConstr(x1: Real, x2: Real): Real = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5 &&
      x1 +/- 1e-11 && x2 +/- 1e-11 &&
      x1*x1 + x2*x2 <= 404.0)

    val t = (3*x1*x1 + 2*x2 - x1)

    x1 + ((2*x1*(t/(x1*x1 + 1))*
    (t/(x1*x1 + 1) - 3) + x1*x1*(4*(t/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(t/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1)))
  }

  def jetEngineRef2Constr(x1: Real, x2: Real): Real = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5  &&
      x1*x1 + x2*x2 <= 404.0)

    val t = ((3*x1*x1 + 2*x2 - x1))/(x1*x1 + 1)

    x1 + ((2*x1*(t)*
    (t - 3) + x1*x1*(4*(t)-6))*
    (x1*x1 + 1) + 3*x1*x1*(t) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1)))
  }

  def jetEngineRef2ErrConstr(x1: Real, x2: Real): Real = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5 &&
      x1 +/- 1e-11 && x2 +/- 1e-11  &&
      x1*x1 + x2*x2 <= 404.0)

    val t = ((3*x1*x1 + 2*x2 - x1))/(x1*x1 + 1)

    x1 + ((2*x1*(t)*
    (t - 3) + x1*x1*(4*(t)-6))*
    (x1*x1 + 1) + 3*x1*x1*(t) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1)))
  }

  def turbine1RefConstr(v: Real, w: Real, r: Real): Real = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8 &&
      v*v + w*w + r*r <= 62.0)

    val t = w*w*r*r
    3 + 2/(r*r) - 0.125*(3-2*v)*(t)/(1-v) - 4.5

  }

  def turbine1RefErrConstr(v: Real, w: Real, r: Real): Real = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8 &&
      v*v + w*w + r*r <= 62.0 &&
      v +/- 1e-11 && w +/- 1e-11 && r +/- 1e-11)

    val t = w*w*r*r
    3 + 2/(r*r) - 0.125*(3-2*v)*(t)/(1-v) - 4.5

  }


  def turbine2RefConstr(v: Real, w: Real, r: Real): Real = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8 &&
      v*v + w*w + r*r <= 62.0)

    val t = w*w*r*r
    6*v - 0.5 * v * (t) / (1-v) - 2.5

  }

  def turbine2RefErrConstr(v: Real, w: Real, r: Real): Real = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8 &&
      v*v + w*w + r*r <= 62.0 &&
      v +/- 1e-11 && w +/- 1e-11 && r +/- 1e-11)

    val t = w*w*r*r
    6*v - 0.5 * v * (t) / (1-v) - 2.5

  }

  def turbine3Ref(v: Real, w: Real, r: Real): Real = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8 &&
      v*v + w*w + r*r <= 62.0)

    val t = w*w*r*r
    3 - 2/(r*r) - 0.125 * (1+2*v) * (t) / (1-v) - 0.5

  }


  def turbine3RefErrConstr(v: Real, w: Real, r: Real): Real = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8 &&
      v*v + w*w + r*r <= 62.0 &&
      v +/- 1e-11 && w +/- 1e-11 && r +/- 1e-11)

    val t = w*w*r*r
    3 - 2/(r*r) - 0.125 * (1+2*v) * (t) / (1-v) - 0.5

  }


  /*def sineConstr(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 - (x*x*x*x*x*x*x)/5040.0
  }

  def sqroot(x: Real): Real = {
    require(x >= 0.0 && x < 10.0)
    1.0 + 0.5*x - 0.125*x*x + 0.0625*x*x*x - 0.0390625*x*x*x*x
  }

  def sineOrder3(x: Real): Real = {
    require(-2.0 < x && x < 2.0)
    0.954929658551372 * x -  0.12900613773279798*(x*x*x)
  }*/


  /*def verhulst(r: Real, K: Real, x: Real): Real = {
    require(r >= 4.0 && r <= 4.0 && K >= 1.11 && K <= 1.11 && 0.1 <= x && x <= 0.3)

    (r*x) / (1 + (x/K))

  }

  def predatorPrey(r: Real, K: Real, x: Real): Real = {
    require(r >= 4.0 && r <= 4.0 && K >= 1.11 && K <= 1.11 && 0.1 <= x && x <= 0.3)

    (r*x*x) / (1 + (x/K)*(x/K))

  }

  def carbonGas(T: Real, a: Real, b: Real, N: Real, p: Real, V: Real): Real = {
    require(T >= 300 && T <= 300 && a >= 0.401 && a <= 0.401 && b >= 42.7e-6 && b <= 42.7e-6 && N >= 1000 && N <= 1000 &&
    p >= 3.5e7 && p <= 3.5e7 && 0.1 < V && V < 0.5)

    val k = 1.3806503e-23
    (p + a * (N / V) * (N / V)) * (V - N * b) - k * N * T

  }*/
}