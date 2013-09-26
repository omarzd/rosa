import leon.Real
import Real._

// For rewriting maybe?
object PhysicsEquations {

  def doppler(u: Real, v: Real, T: Real): Real = {
    require(u >< (-100, 100) && v >< (20, 20000) && T >< (-30, 50) &&)

    (- (331.4 + 0.6 * T) *v) / ((331.4 + 0.6*T + u)*(331.4 + 0.6*T + u))

  }


  def verhulst(r: Real, K: Real, x: Real): Real = {
    require(r >= 4.0 && r <= 4.0 && K >= 1.11 && K <= 1.11 && x.in(0.1, 0.3) && r +/- 0.001 && K +/- 1e-5 && x +/- 1e-6)

    (r*x) / (1 + (x/K))

  }

  def predatorPrey(r: Real, K: Real, x: Real): Real = {
    require(r >= 4.0 && r <= 4.0 && K >= 1.11 && K <= 1.11 && x.in(0.1, 0.3) && r +/- 0.001 && K +/- 1e-5 && x +/- 1e-6)

    (r*x*x) / (1 + (x/K)*(x/K))

  }

  def carbonGas(T: Real, a: Real, b: Real, N: Real, p: Real, V: Real): Real = {
    require(T >= 300 && T <= 300 && a >= 0.401 && a <= 0.401 && b >= 42.7e-6 && b <= 42.7e-6 && N >= 1000 && N <= 1000 &&
    p >= 3.5e7 && p <= 3.5e7 && V.in(0.1, 0.5) && T +/- 0.01 && a +/- 1e-6 && b +/- 1e-10 && N +/- 5 && p +/- 1e-13 && V +/- 0.005)

    val k = 1.3806503e-23
    (p + a * (N / V) * (N / V)) * (V - N * b) - k * N * T

  }

  
}