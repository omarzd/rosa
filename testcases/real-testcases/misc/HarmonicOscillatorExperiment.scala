import leon.Real
import Real._


object HarmonicOscillatorExperiment {

  def eulerSpringUnrolled1(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    
    val x0 = x + v*dt
    val v0 = v + (-(k*x*dt))  

    x0
  }

  def eulerSpringUnrolled2(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    
    val x0 = x + v*dt
    val v0 = v + (-(k*x*dt))  

    val x1 = x0 + v0*dt
    val v1 = v0 + (-(k*x0*dt)) 

    x1
  }

  def eulerSpringUnrolled3(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    
    val x0 = x + v*dt
    val v0 = v + (-(k*x*dt))  

    val x1 = x0 + v0*dt
    val v1 = v0 + (-(k*x0*dt)) 

    val x2 = x1 + v1*dt
    val v2 = v1 + (-(k*x1*dt))

    x2
  }

  def eulerSpringUnrolled4(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    
    val x0 = x + v*dt
    val v0 = v + (-(k*x*dt))  

    val x1 = x0 + v0*dt
    val v1 = v0 + (-(k*x0*dt)) 

    val x2 = x1 + v1*dt
    val v2 = v1 + (-(k*x1*dt))

    val x3 = x2 + v2*dt
    val v3 = v2 + (-(k*x2*dt))  
    
    x3
  }

  def eulerSpringUnrolled5(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    
    val x0 = x + v*dt
    val v0 = v + (-(k*x*dt))  

    val x1 = x0 + v0*dt
    val v1 = v0 + (-(k*x0*dt)) 

    val x2 = x1 + v1*dt
    val v2 = v1 + (-(k*x1*dt))

    val x3 = x2 + v2*dt
    val v3 = v2 + (-(k*x2*dt))  
    
    val x4 = x3 + v3*dt
    val v4 = v3 + (-(k*x3*dt))  
    
    x4
  }

  def eulerSpringUnrolled6(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    
    val x0 = x + v*dt
    val v0 = v + (-(k*x*dt))  

    val x1 = x0 + v0*dt
    val v1 = v0 + (-(k*x0*dt)) 

    val x2 = x1 + v1*dt
    val v2 = v1 + (-(k*x1*dt))

    val x3 = x2 + v2*dt
    val v3 = v2 + (-(k*x2*dt))  
    
    val x4 = x3 + v3*dt
    val v4 = v3 + (-(k*x3*dt))  
    
    val x5 = x4 + v4*dt
    val v5 = v4 + (-(k*x4*dt))  
    
    x5
  } 

  def eulerSpringUnrolled7(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    
    val x0 = x + v*dt
    val v0 = v + (-(k*x*dt))  

    val x1 = x0 + v0*dt
    val v1 = v0 + (-(k*x0*dt)) 

    val x2 = x1 + v1*dt
    val v2 = v1 + (-(k*x1*dt))

    val x3 = x2 + v2*dt
    val v3 = v2 + (-(k*x2*dt))  
    
    val x4 = x3 + v3*dt
    val v4 = v3 + (-(k*x3*dt))  
    
    val x5 = x4 + v4*dt
    val v5 = v4 + (-(k*x4*dt))  
    
    val x6 = x5 + v5*dt
    val v6 = v5 + (-(k*x5*dt))  
    
    x6
  } 

  def eulerSpringUnrolled8(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    
    val x0 = x + v*dt
    val v0 = v + (-(k*x*dt))  

    val x1 = x0 + v0*dt
    val v1 = v0 + (-(k*x0*dt)) 

    val x2 = x1 + v1*dt
    val v2 = v1 + (-(k*x1*dt))

    val x3 = x2 + v2*dt
    val v3 = v2 + (-(k*x2*dt))  
    
    val x4 = x3 + v3*dt
    val v4 = v3 + (-(k*x3*dt))  
    
    val x5 = x4 + v4*dt
    val v5 = v4 + (-(k*x4*dt))  
    
    val x6 = x5 + v5*dt
    val v6 = v5 + (-(k*x5*dt))  
    
    val x7 = x6 + v6*dt
    val v7 = v6 + (-(k*x6*dt))  
  
    x7
  } 

  def eulerSpringUnrolled9(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    
    val x0 = x + v*dt
    val v0 = v + (-(k*x*dt))  

    val x1 = x0 + v0*dt
    val v1 = v0 + (-(k*x0*dt)) 

    val x2 = x1 + v1*dt
    val v2 = v1 + (-(k*x1*dt))

    val x3 = x2 + v2*dt
    val v3 = v2 + (-(k*x2*dt))  
    
    val x4 = x3 + v3*dt
    val v4 = v3 + (-(k*x3*dt))  
    
    val x5 = x4 + v4*dt
    val v5 = v4 + (-(k*x4*dt))  
    
    val x6 = x5 + v5*dt
    val v6 = v5 + (-(k*x5*dt))  
    
    val x7 = x6 + v6*dt
    val v7 = v6 + (-(k*x6*dt))  
    
    val x8 = x7 + v7*dt
    val v8 = v7 + (-(k*x7*dt))  
    
    x8
  } 

  def eulerSpringUnrolled10(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    
    val x0 = x + v*dt
    val v0 = v + (-(k*x*dt))  

    val x1 = x0 + v0*dt
    val v1 = v0 + (-(k*x0*dt)) 

    val x2 = x1 + v1*dt
    val v2 = v1 + (-(k*x1*dt))

    val x3 = x2 + v2*dt
    val v3 = v2 + (-(k*x2*dt))  
    
    val x4 = x3 + v3*dt
    val v4 = v3 + (-(k*x3*dt))  
    
    val x5 = x4 + v4*dt
    val v5 = v4 + (-(k*x4*dt))  
    
    val x6 = x5 + v5*dt
    val v6 = v5 + (-(k*x5*dt))  
    
    val x7 = x6 + v6*dt
    val v7 = v6 + (-(k*x6*dt))  
    
    val x8 = x7 + v7*dt
    val v8 = v7 + (-(k*x7*dt))  
    
    val x9 = x8 + v8*dt
    val v9 = v8 + (-(k*x8*dt))
    x9
  }

  def eulerSpringUnrolled11(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    
    val x0 = x + v*dt
    val v0 = v + (-(k*x*dt))  

    val x1 = x0 + v0*dt
    val v1 = v0 + (-(k*x0*dt)) 

    val x2 = x1 + v1*dt
    val v2 = v1 + (-(k*x1*dt))

    val x3 = x2 + v2*dt
    val v3 = v2 + (-(k*x2*dt))  
    
    val x4 = x3 + v3*dt
    val v4 = v3 + (-(k*x3*dt))  
    
    val x5 = x4 + v4*dt
    val v5 = v4 + (-(k*x4*dt))  
    
    val x6 = x5 + v5*dt
    val v6 = v5 + (-(k*x5*dt))  
    
    val x7 = x6 + v6*dt
    val v7 = v6 + (-(k*x6*dt))  
    
    val x8 = x7 + v7*dt
    val v8 = v7 + (-(k*x7*dt))  
    
    val x9 = x8 + v8*dt
    val v9 = v8 + (-(k*x8*dt))

    val x10 = x9 + v9*dt
    val v10 = v9 + (-(k*x9*dt))
    x10
  } 

  def eulerSpringUnrolled12(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    
    val x0 = x + v*dt
    val v0 = v + (-(k*x*dt))  

    val x1 = x0 + v0*dt
    val v1 = v0 + (-(k*x0*dt)) 

    val x2 = x1 + v1*dt
    val v2 = v1 + (-(k*x1*dt))

    val x3 = x2 + v2*dt
    val v3 = v2 + (-(k*x2*dt))  
    
    val x4 = x3 + v3*dt
    val v4 = v3 + (-(k*x3*dt))  
    
    val x5 = x4 + v4*dt
    val v5 = v4 + (-(k*x4*dt))  
    
    val x6 = x5 + v5*dt
    val v6 = v5 + (-(k*x5*dt))  
    
    val x7 = x6 + v6*dt
    val v7 = v6 + (-(k*x6*dt))  
    
    val x8 = x7 + v7*dt
    val v8 = v7 + (-(k*x7*dt))  
    
    val x9 = x8 + v8*dt
    val v9 = v8 + (-(k*x8*dt))

    val x10 = x9 + v9*dt
    val v10 = v9 + (-(k*x9*dt))

    val x11 = x10 + v10*dt
    val v11 = v10 + (-(k*x10*dt))
    x11
  } 

  def eulerSpringUnrolled13(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    
    val x0 = x + v*dt
    val v0 = v + (-(k*x*dt))  

    val x1 = x0 + v0*dt
    val v1 = v0 + (-(k*x0*dt)) 

    val x2 = x1 + v1*dt
    val v2 = v1 + (-(k*x1*dt))

    val x3 = x2 + v2*dt
    val v3 = v2 + (-(k*x2*dt))  
    
    val x4 = x3 + v3*dt
    val v4 = v3 + (-(k*x3*dt))  
    
    val x5 = x4 + v4*dt
    val v5 = v4 + (-(k*x4*dt))  
    
    val x6 = x5 + v5*dt
    val v6 = v5 + (-(k*x5*dt))  
    
    val x7 = x6 + v6*dt
    val v7 = v6 + (-(k*x6*dt))  
    
    val x8 = x7 + v7*dt
    val v8 = v7 + (-(k*x7*dt))  
    
    val x9 = x8 + v8*dt
    val v9 = v8 + (-(k*x8*dt))

    val x10 = x9 + v9*dt
    val v10 = v9 + (-(k*x9*dt))

    val x11 = x10 + v10*dt
    val v11 = v10 + (-(k*x10*dt))

    val x12 = x11 + v11*dt
    val v12 = v11 + (-(k*x11*dt))
    x12
  } 

  def eulerSpringUnrolled14(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    
    val x0 = x + v*dt
    val v0 = v + (-(k*x*dt))  

    val x1 = x0 + v0*dt
    val v1 = v0 + (-(k*x0*dt)) 

    val x2 = x1 + v1*dt
    val v2 = v1 + (-(k*x1*dt))

    val x3 = x2 + v2*dt
    val v3 = v2 + (-(k*x2*dt))  
    
    val x4 = x3 + v3*dt
    val v4 = v3 + (-(k*x3*dt))  
    
    val x5 = x4 + v4*dt
    val v5 = v4 + (-(k*x4*dt))  
    
    val x6 = x5 + v5*dt
    val v6 = v5 + (-(k*x5*dt))  
    
    val x7 = x6 + v6*dt
    val v7 = v6 + (-(k*x6*dt))  
    
    val x8 = x7 + v7*dt
    val v8 = v7 + (-(k*x7*dt))  
    
    val x9 = x8 + v8*dt
    val v9 = v8 + (-(k*x8*dt))

    val x10 = x9 + v9*dt
    val v10 = v9 + (-(k*x9*dt))

    val x11 = x10 + v10*dt
    val v11 = v10 + (-(k*x10*dt))

    val x12 = x11 + v11*dt
    val v12 = v11 + (-(k*x11*dt))

    val x13 = x12 + v12*dt
    val v13 = v12 + (-(k*x12*dt))
    x13
  } 

  def eulerSpringUnrolled15(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    
    val x0 = x + v*dt
    val v0 = v + (-(k*x*dt))  

    val x1 = x0 + v0*dt
    val v1 = v0 + (-(k*x0*dt)) 

    val x2 = x1 + v1*dt
    val v2 = v1 + (-(k*x1*dt))

    val x3 = x2 + v2*dt
    val v3 = v2 + (-(k*x2*dt))  
    
    val x4 = x3 + v3*dt
    val v4 = v3 + (-(k*x3*dt))  
    
    val x5 = x4 + v4*dt
    val v5 = v4 + (-(k*x4*dt))  
    
    val x6 = x5 + v5*dt
    val v6 = v5 + (-(k*x5*dt))  
    
    val x7 = x6 + v6*dt
    val v7 = v6 + (-(k*x6*dt))  
    
    val x8 = x7 + v7*dt
    val v8 = v7 + (-(k*x7*dt))  
    
    val x9 = x8 + v8*dt
    val v9 = v8 + (-(k*x8*dt))

    val x10 = x9 + v9*dt
    val v10 = v9 + (-(k*x9*dt))

    val x11 = x10 + v10*dt
    val v11 = v10 + (-(k*x10*dt))

    val x12 = x11 + v11*dt
    val v12 = v11 + (-(k*x11*dt))

    val x13 = x12 + v12*dt
    val v13 = v12 + (-(k*x12*dt))

    val x14 = x13 + v13*dt
    val v14 = v13 + (-(k*x13*dt))
    x14
  }
}