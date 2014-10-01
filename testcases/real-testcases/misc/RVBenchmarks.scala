
import leon.Real
import Real._
import math.{exp, sin, cos}

object RVBenchmarks {
  //Unary
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



  // Multivariate

  //Array(0.9, 0.2)
  def circleParabola1(x: Real, y: Real): Real = {
    require(x.in(0.7, 3.5) && y.in(-3.5, 3.7) && noise(x,1e-7) && noise(y,1e-9))

    x*x - 2*x - y + 1.0
  }

  def circleParabola2(x: Real, y: Real): Real = {
    require(x.in(0.7, 3.5) && y.in(-3.5, 3.7) && noise(x,1e-7) && noise(y,1e-9))
    
    x*x + y*y - 1.0
  }

  def noNameQuadratic1(x: Real, y: Real): Real = {
    require(x.in(-6.8, -1.5) && y.in(3.4, 9.6) && noise(x,1e-8) && noise(y,1e-10))
    
    x*x + y*y - 4*x
  }

  def noNameQuadratic2(x: Real, y: Real): Real = {
    require(x.in(-6.8, -1.5) && y.in(3.4, 9.6) && noise(x,1e-8) && noise(y,1e-10))
    
    y*y + 2*x - 2.0
  }


  def anotherQuadratic1(x1: Real, x2: Real, x3: Real): Real = {
    require(x1.in(-2.3, 1.3) && x2.in(3.2, 4.5) && x3.in(-5.4, -0.5) &&
     noise(x1,1e-8) && noise(x2,1e-7) && noise(x3,1e-9))
    
    4*x1*x1 + 2*x2 - 4.0
  }

  def anotherQuadratic2(x1: Real, x2: Real, x3: Real): Real = {
    require(x1.in(-2.3, 1.3) && x2.in(3.2, 4.5) && x3.in(-5.4, -0.5) &&
     noise(x1,1e-8) && noise(x2,1e-7) && noise(x3,1e-9))

    x1 + 2*x2*x2 + 2*x3 - 4.0
  }

  def anotherQuadratic3(x1: Real, x2: Real, x3: Real): Real = {
    require(x1.in(-2.3, 1.3) && x2.in(3.2, 4.5) && x3.in(-5.4, -0.5) &&
     noise(x1,1e-8) && noise(x2,1e-7) && noise(x3,1e-9))
    
    x2 + 2*x3*x3 - 4.0
  }

  def turbine1(v: Real, w: Real, r: Real): Real = {
    require(v.in(-4.5, -0.3) && w.in(0.4, 0.9) && r.in(3.8, 7.8) &&
     noise(v,1e-7) && noise(w,1e-12) && noise(r,1e-8))
    
    3 + 2/(r*r) - 0.125*(3-2*v)*(w*w*r*r)/(1-v) - 4.5  
  }
  
  def turbine2(v: Real, w: Real, r: Real): Real = {
    require(v.in(-4.5, -0.3) && w.in(0.4, 0.9) && r.in(3.8, 7.8) &&
     noise(v,1e-7) && noise(w,1e-12) && noise(r,1e-8))
    
    6*v - 0.5 * v * (w*w*r*r) / (1-v) - 2.5
  }

  def turbine3(v: Real, w: Real, r: Real): Real = {
    require(v.in(-4.5, -0.3) && w.in(0.4, 0.9) && r.in(3.8, 7.8) &&
     noise(v,1e-7) && noise(w,1e-12) && noise(r,1e-8))
    
    3 - 2/(r*r) - 0.125 * (1+2*v) * (w*w*r*r) / (1-v) - 0.5
  }


  /*def stressDistribution1(x1: Real, x2: Real): Real = {
  
    cos(2*x1) - cos(2*x2) - 0.4
  }
  
  def stressDistribution2(x1: Real, x2: Real): Real = {
  
    2*(x2 - x1) + sin(2*x2) - sin(2*x1) - 1.2
  }

  def sinCosSystem1(x1: Real, x2: Real): Real = {

    x1 * cos(x2) + x2 * cos(x1) - 0.9
  }
 
  def sinCosSystem2(x1: Real, x2: Real): Real = {

    x1 * sin(x2) + x2 * sin(x1) - 0.1
  }

  def doublePendulum1(x1: Real, x2: Real): Real = {

    tan(x1) - k * (2*sin(x1) + sin(x2))

  }

  def doublePendulum2(x1: Real, x2: Real): Real = {

    tan(x2) - 2*k * (sin(x1) + sin(x2))
  }*/


}
