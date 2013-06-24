
import leon.Real
import Real._
import math.{exp, sin, cos}

object MultivariateRVBenchmarks {

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
