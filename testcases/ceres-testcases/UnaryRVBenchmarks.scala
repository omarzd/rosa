
import leon.Real
import Real._
//import math.{exp, sin, cos}

object UnaryRVBenchmarks {

  def verhulst(r: Real, K: Real, x: Real): Real = {
    require(r >= 4.0 && r <= 4.0 && K >= 1.11 && K <= 1.11 && x.in(0.1, 0.3) &&
      noise(r, 0.001) && noise(K, 1e-5) && noise(x, 1e-6))

    (r*x) / (1 + (x/K))

  } ensuring (res => res <= 0.0)

  def predatorPrey(r: Real, K: Real, x: Real): Real = {
    require(r >= 4.0 && r <= 4.0 && K >= 1.11 && K <= 1.11 && x.in(0.1, 0.3) &&
      noise(r, 0.001) && noise(K, 1e-5) && noise(x, 1e-6))

    (r*x*x) / (1 + (x/K)*(x/K))

  }  ensuring (res => res <= 0.0)


  def carbonGas(T: Real, a: Real, b: Real, N: Real, p: Real, V: Real): Real = {
    require(T >= 300 && T <= 300 && a >= 0.401 && a <= 0.401 && b >= 42.7e-6 && b <= 42.7e-6 && N >= 1000 && N <= 1000 &&
    p >= 3.5e7 && p <= 3.5e7 && V.in(0.1, 0.5) &&
    noise(T, 0.01) && noise(a, 1e-6) && noise(b, 1e-10) && noise(N, 5) &&
    noise(p, 1e-13) && noise(V, 0.005))

    val k = 1.3806503e-23
    (p + a * (N / V) * (N / V)) * (V - N * b) - k * N * T

  }  ensuring (res => res <= 0.0)


 
  // val x0 = 1.2
  def polynomial1(x: Real): Real = {
    require(x.in(-9.6, 7.5) && noise(x, 0.2))
    x*x*x/3.0 - 2 * x*x + 4.5

  }  ensuring (res => res <= 0.0)

  // val x0 = 6.5
  def polynomial2(x: Real): Real = {
    require(x.in(4.5, 7.8) && noise(x, 1e-4))
    x*x*x*x*x*x + 4.2*x*x*x*x*x -72.3*x*x*x*x -214.4*x*x*x + 1127.1*x*x + 1602.9*x - 5040.5

  }  ensuring (res => res <= 0.0)


  // val a1 = 10.0; val a2 = 13.0; val a3 = 8.0; val a4 = 10.0
  //  val b = 0.4; val x0 = -0.1
  /* def rods(a1: Real, a2: Real, a3: Real, a4: Real, b: Real, x: Real): Real = {

    a1/a2 * cos(b) - a1/a4 * cos(x) - cos(b - x) +
      (a1*a1 + a2*a2 - a3*a3 + a4*a4)/(2*a2*a4)

  }*/
  // val alpha = 0.2; val beta = 2.0; val x0 = 2.0
  /*def bulmerVolmer(alpha: Real, beta: Real, x: Real): Real = {

    exp(alpha*x) - exp(-(1 - alpha)*x) - beta

  }*/

  // val x0 = 1.6
  /*def sinXSquared(x: Real): Real = {
  
    (x/2)*(x/2) - sin(x)

  }*/

  // val x0 = 1.7
  /*def exponents(x: Real): Real = {
    
    exp(x)*(x - 1) - exp(-x)*(x + 1)

  }*/


}
