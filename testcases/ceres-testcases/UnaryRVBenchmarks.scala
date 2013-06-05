
import leon.Real
import Real._
import math.{exp, sin, cos}

object UnaryRVBenchmarks {

  // val r = 4.0; val K = 1.11; val x0 = 0.1
  def verhulst(r: Real, K: Real, x: Real): Real = {

    (r*x) / (1 + (x/K))

  }

  // val r = 4.0; val K = 1.11; val x0 = 0.7
  def predatorPrey(r: Real, K: Real, x: Real): Real = {

    (r*x*x) / (1 + (x/K)*(x/K))

  }


  // val T = 300; val a = 0.401; val b = 42.7e-6; val N = 1000
  // val p = 3.5e7; val k = 1.3806503e-23; val x0 = 0.1
  def carbonGas(T: Real, a: Real, b: Real, N: Real, p: Real, x: Real): Real = {
    val k = 1.3806503e-23

    (p + a * (N / V) * (N / V)) * (V - N * b) - k * N * T

  }

 
  // val x0 = 1.2
  def polynomial1(x: Real): Real = {
  
    x*x*x/3.0 - 2 * x*x + 4.5

  }

  // val x0 = 6.5
  def polynomial2(x: Real): Real = {

    x*x*x*x*x*x + 4.2*x*x*x*x*x -72.3*x*x*x*x -214.4*x*x*x + 1127.1*x*x + 1602.9*x - 5040.5

  }


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
