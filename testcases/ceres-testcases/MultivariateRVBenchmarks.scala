
import leon.Real
import Real._
import math.{exp, sin, cos}

object MultivariateRVBenchmarks {
  def circleParabola1(x: Real, y: Real): Real = {

    x*x - 2*x - y + 1.0
  }

  def circleParabola2(x: Real, y: Real): Real = {

    x*x + y*y - 1.0
  }

  def noNameQuadratic1(x: Real, y: Real): Real = {

    x*x + y*y - 4*x
  }

  def noNameQuadratic2(x: Real, y: Real): Real = {

    y*y + 2*x - 2.0
  }


  def anotherQuadratic1(x1: Real, x2: Real, x3: Real): Real = {

    4*x1*x1 + 2*x2 - 4.0
  }

  def anotherQuadratic2(x1: Real, x2: Real, x3: Real): Real = {

    x1 + 2*x2*x2 + 2*x3 - 4.0
  }

  def anotherQuadratic3(x1: Real, x2: Real, x3: Real): Real = {

    x2 + 2*x3*x3 - 4.0
  }

  def turbine1(v: Real, w: Real, r: Real): Real = {

    3 + 2/(r*r) - 0.125*(3-2*v)*(w*w*r*r)/(1-v) - 4.5  
  }
  
  def turbine2(v: Real, w: Real, r: Real): Real = {

    6*v - 0.5 * v * (w*w*r*r) / (1-v) - 2.5
  }

  def turbine3(v: Real, w: Real, r: Real): Real = {

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
