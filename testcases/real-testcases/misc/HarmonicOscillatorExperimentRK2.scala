import leon.Real
import Real._


object HarmonicOscillatorExperimentRK2 {

  def rk2SpringUnrolled1(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    val x0 = x + dt * (v + (-(k*x)*dt/2))
    val v0 = v + dt * (-double2real(k))* (x + v*dt/2)

    x0
  }

  def rk2SpringUnrolled2(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    val x0 = x + dt * (v + (-(k*x)*dt/2))
    val v0 = v + dt * (-double2real(k))* (x + v*dt/2)

    val x1 = x0 + dt * (v0 + (-(k*x0)*dt/2))
    val v1 = v0 + dt * (-double2real(k))* (x0 + v0*dt/2)

    x1
  }

  def rk2SpringUnrolled3(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    val x0 = x + dt * (v + (-(k*x)*dt/2))
    val v0 = v + dt * (-double2real(k))* (x + v*dt/2)

    val x1 = x0 + dt * (v0 + (-(k*x0)*dt/2))
    val v1 = v0 + dt * (-double2real(k))* (x0 + v0*dt/2)

    val x2 = x1 + dt * (v1 + (-(k*x1)*dt/2))
    val v2 = v1 + dt * (-double2real(k))* (x1 + v1*dt/2)

    x2
  }

  def rk2SpringUnrolled4(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    val x0 = x + dt * (v + (-(k*x)*dt/2))
    val v0 = v + dt * (-double2real(k))* (x + v*dt/2)

    val x1 = x0 + dt * (v0 + (-(k*x0)*dt/2))
    val v1 = v0 + dt * (-double2real(k))* (x0 + v0*dt/2)

    val x2 = x1 + dt * (v1 + (-(k*x1)*dt/2))
    val v2 = v1 + dt * (-double2real(k))* (x1 + v1*dt/2)

    val x3 = x2 + dt * (v2 + (-(k*x2)*dt/2))
    val v3 = v2 + dt * (-double2real(k))* (x2 + v2*dt/2)
    
    x3
  }

  def rk2SpringUnrolled5(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    val x0 = x + dt * (v + (-(k*x)*dt/2))
    val v0 = v + dt * (-double2real(k))* (x + v*dt/2)

    val x1 = x0 + dt * (v0 + (-(k*x0)*dt/2))
    val v1 = v0 + dt * (-double2real(k))* (x0 + v0*dt/2)

    val x2 = x1 + dt * (v1 + (-(k*x1)*dt/2))
    val v2 = v1 + dt * (-double2real(k))* (x1 + v1*dt/2)

    val x3 = x2 + dt * (v2 + (-(k*x2)*dt/2))
    val v3 = v2 + dt * (-double2real(k))* (x2 + v2*dt/2)

    val x4 = x3 + dt * (v3 + (-(k*x3)*dt/2))
    val v4 = v3 + dt * (-double2real(k))* (x3 + v3*dt/2)
    
    x4
  }

  def rk2SpringUnrolled6(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    val x0 = x + dt * (v + (-(k*x)*dt/2))
    val v0 = v + dt * (-double2real(k))* (x + v*dt/2)

    val x1 = x0 + dt * (v0 + (-(k*x0)*dt/2))
    val v1 = v0 + dt * (-double2real(k))* (x0 + v0*dt/2)

    val x2 = x1 + dt * (v1 + (-(k*x1)*dt/2))
    val v2 = v1 + dt * (-double2real(k))* (x1 + v1*dt/2)

    val x3 = x2 + dt * (v2 + (-(k*x2)*dt/2))
    val v3 = v2 + dt * (-double2real(k))* (x2 + v2*dt/2)

    val x4 = x3 + dt * (v3 + (-(k*x3)*dt/2))
    val v4 = v3 + dt * (-double2real(k))* (x3 + v3*dt/2)

    val x5 = x4 + dt * (v4 + (-(k*x4)*dt/2))
    val v5 = v4 + dt * (-double2real(k))* (x4 + v4*dt/2)
    
    x5
  } 

  def rk2SpringUnrolled7(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    val x0 = x + dt * (v + (-(k*x)*dt/2))
    val v0 = v + dt * (-double2real(k))* (x + v*dt/2)

    val x1 = x0 + dt * (v0 + (-(k*x0)*dt/2))
    val v1 = v0 + dt * (-double2real(k))* (x0 + v0*dt/2)

    val x2 = x1 + dt * (v1 + (-(k*x1)*dt/2))
    val v2 = v1 + dt * (-double2real(k))* (x1 + v1*dt/2)

    val x3 = x2 + dt * (v2 + (-(k*x2)*dt/2))
    val v3 = v2 + dt * (-double2real(k))* (x2 + v2*dt/2)

    val x4 = x3 + dt * (v3 + (-(k*x3)*dt/2))
    val v4 = v3 + dt * (-double2real(k))* (x3 + v3*dt/2)

    val x5 = x4 + dt * (v4 + (-(k*x4)*dt/2))
    val v5 = v4 + dt * (-double2real(k))* (x4 + v4*dt/2)

    val x6 = x5 + dt * (v5 + (-(k*x5)*dt/2))
    val v6 = v5 + dt * (-double2real(k))* (x5 + v5*dt/2)
    
    x6
  } 

  def rk2SpringUnrolled8(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    val x0 = x + dt * (v + (-(k*x)*dt/2))
    val v0 = v + dt * (-double2real(k))* (x + v*dt/2)

    val x1 = x0 + dt * (v0 + (-(k*x0)*dt/2))
    val v1 = v0 + dt * (-double2real(k))* (x0 + v0*dt/2)

    val x2 = x1 + dt * (v1 + (-(k*x1)*dt/2))
    val v2 = v1 + dt * (-double2real(k))* (x1 + v1*dt/2)

    val x3 = x2 + dt * (v2 + (-(k*x2)*dt/2))
    val v3 = v2 + dt * (-double2real(k))* (x2 + v2*dt/2)

    val x4 = x3 + dt * (v3 + (-(k*x3)*dt/2))
    val v4 = v3 + dt * (-double2real(k))* (x3 + v3*dt/2)

    val x5 = x4 + dt * (v4 + (-(k*x4)*dt/2))
    val v5 = v4 + dt * (-double2real(k))* (x4 + v4*dt/2)

    val x6 = x5 + dt * (v5 + (-(k*x5)*dt/2))
    val v6 = v5 + dt * (-double2real(k))* (x5 + v5*dt/2)

    val x7 = x6 + dt * (v6 + (-(k*x6)*dt/2))
    val v7 = v6 + dt * (-double2real(k))* (x6 + v6*dt/2)
   
    x7
  } 

  def rk2SpringUnrolled9(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    
    val x0 = x + dt * (v + (-(k*x)*dt/2))
    val v0 = v + dt * (-double2real(k))* (x + v*dt/2)

    val x1 = x0 + dt * (v0 + (-(k*x0)*dt/2))
    val v1 = v0 + dt * (-double2real(k))* (x0 + v0*dt/2)

    val x2 = x1 + dt * (v1 + (-(k*x1)*dt/2))
    val v2 = v1 + dt * (-double2real(k))* (x1 + v1*dt/2)

    val x3 = x2 + dt * (v2 + (-(k*x2)*dt/2))
    val v3 = v2 + dt * (-double2real(k))* (x2 + v2*dt/2)

    val x4 = x3 + dt * (v3 + (-(k*x3)*dt/2))
    val v4 = v3 + dt * (-double2real(k))* (x3 + v3*dt/2)

    val x5 = x4 + dt * (v4 + (-(k*x4)*dt/2))
    val v5 = v4 + dt * (-double2real(k))* (x4 + v4*dt/2)

    val x6 = x5 + dt * (v5 + (-(k*x5)*dt/2))
    val v6 = v5 + dt * (-double2real(k))* (x5 + v5*dt/2)

    val x7 = x6 + dt * (v6 + (-(k*x6)*dt/2))
    val v7 = v6 + dt * (-double2real(k))* (x6 + v6*dt/2)
    
    val x8 = x7 + dt * (v7 + (-(k*x7)*dt/2))
    val v8 = v7 + dt * (-double2real(k))* (x7 + v7*dt/2)

    x8
  } 

  def rk2SpringUnrolled10(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    
    val x0 = x + dt * (v + (-(k*x)*dt/2))
    val v0 = v + dt * (-double2real(k))* (x + v*dt/2)

    val x1 = x0 + dt * (v0 + (-(k*x0)*dt/2))
    val v1 = v0 + dt * (-double2real(k))* (x0 + v0*dt/2)

    val x2 = x1 + dt * (v1 + (-(k*x1)*dt/2))
    val v2 = v1 + dt * (-double2real(k))* (x1 + v1*dt/2)

    val x3 = x2 + dt * (v2 + (-(k*x2)*dt/2))
    val v3 = v2 + dt * (-double2real(k))* (x2 + v2*dt/2)

    val x4 = x3 + dt * (v3 + (-(k*x3)*dt/2))
    val v4 = v3 + dt * (-double2real(k))* (x3 + v3*dt/2)

    val x5 = x4 + dt * (v4 + (-(k*x4)*dt/2))
    val v5 = v4 + dt * (-double2real(k))* (x4 + v4*dt/2)

    val x6 = x5 + dt * (v5 + (-(k*x5)*dt/2))
    val v6 = v5 + dt * (-double2real(k))* (x5 + v5*dt/2)

    val x7 = x6 + dt * (v6 + (-(k*x6)*dt/2))
    val v7 = v6 + dt * (-double2real(k))* (x6 + v6*dt/2)
    
    val x8 = x7 + dt * (v7 + (-(k*x7)*dt/2))
    val v8 = v7 + dt * (-double2real(k))* (x7 + v7*dt/2)

    val x9 = x8 + dt * (v8 + (-(k*x8)*dt/2))
    val v9 = v8 + dt * (-double2real(k))* (x8 + v8*dt/2)

    x9
  }

  def rk2SpringUnrolled11(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    val x0 = x + dt * (v + (-(k*x)*dt/2))
    val v0 = v + dt * (-double2real(k))* (x + v*dt/2)

    val x1 = x0 + dt * (v0 + (-(k*x0)*dt/2))
    val v1 = v0 + dt * (-double2real(k))* (x0 + v0*dt/2)

    val x2 = x1 + dt * (v1 + (-(k*x1)*dt/2))
    val v2 = v1 + dt * (-double2real(k))* (x1 + v1*dt/2)

    val x3 = x2 + dt * (v2 + (-(k*x2)*dt/2))
    val v3 = v2 + dt * (-double2real(k))* (x2 + v2*dt/2)

    val x4 = x3 + dt * (v3 + (-(k*x3)*dt/2))
    val v4 = v3 + dt * (-double2real(k))* (x3 + v3*dt/2)

    val x5 = x4 + dt * (v4 + (-(k*x4)*dt/2))
    val v5 = v4 + dt * (-double2real(k))* (x4 + v4*dt/2)

    val x6 = x5 + dt * (v5 + (-(k*x5)*dt/2))
    val v6 = v5 + dt * (-double2real(k))* (x5 + v5*dt/2)

    val x7 = x6 + dt * (v6 + (-(k*x6)*dt/2))
    val v7 = v6 + dt * (-double2real(k))* (x6 + v6*dt/2)
    
    val x8 = x7 + dt * (v7 + (-(k*x7)*dt/2))
    val v8 = v7 + dt * (-double2real(k))* (x7 + v7*dt/2)

    val x9 = x8 + dt * (v8 + (-(k*x8)*dt/2))
    val v9 = v8 + dt * (-double2real(k))* (x8 + v8*dt/2)

    val x10 = x9 + dt * (v9 + (-(k*x9)*dt/2))
    val v10 = v9 + dt * (-double2real(k))* (x9 + v9*dt/2)

    x10
  } 

  def rk2SpringUnrolled12(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    val x0 = x + dt * (v + (-(k*x)*dt/2))
    val v0 = v + dt * (-double2real(k))* (x + v*dt/2)

    val x1 = x0 + dt * (v0 + (-(k*x0)*dt/2))
    val v1 = v0 + dt * (-double2real(k))* (x0 + v0*dt/2)

    val x2 = x1 + dt * (v1 + (-(k*x1)*dt/2))
    val v2 = v1 + dt * (-double2real(k))* (x1 + v1*dt/2)

    val x3 = x2 + dt * (v2 + (-(k*x2)*dt/2))
    val v3 = v2 + dt * (-double2real(k))* (x2 + v2*dt/2)

    val x4 = x3 + dt * (v3 + (-(k*x3)*dt/2))
    val v4 = v3 + dt * (-double2real(k))* (x3 + v3*dt/2)

    val x5 = x4 + dt * (v4 + (-(k*x4)*dt/2))
    val v5 = v4 + dt * (-double2real(k))* (x4 + v4*dt/2)

    val x6 = x5 + dt * (v5 + (-(k*x5)*dt/2))
    val v6 = v5 + dt * (-double2real(k))* (x5 + v5*dt/2)

    val x7 = x6 + dt * (v6 + (-(k*x6)*dt/2))
    val v7 = v6 + dt * (-double2real(k))* (x6 + v6*dt/2)
    
    val x8 = x7 + dt * (v7 + (-(k*x7)*dt/2))
    val v8 = v7 + dt * (-double2real(k))* (x7 + v7*dt/2)

    val x9 = x8 + dt * (v8 + (-(k*x8)*dt/2))
    val v9 = v8 + dt * (-double2real(k))* (x8 + v8*dt/2)

    val x10 = x9 + dt * (v9 + (-(k*x9)*dt/2))
    val v10 = v9 + dt * (-double2real(k))* (x9 + v9*dt/2)

    val x11 = x10 + dt * (v10 + (-(k*x10)*dt/2))
    val v11 = v10 + dt * (-double2real(k))* (x10 + v10*dt/2)

    x11
  } 

  def rk2SpringUnrolled13(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    val x0 = x + dt * (v + (-(k*x)*dt/2))
    val v0 = v + dt * (-double2real(k))* (x + v*dt/2)

    val x1 = x0 + dt * (v0 + (-(k*x0)*dt/2))
    val v1 = v0 + dt * (-double2real(k))* (x0 + v0*dt/2)

    val x2 = x1 + dt * (v1 + (-(k*x1)*dt/2))
    val v2 = v1 + dt * (-double2real(k))* (x1 + v1*dt/2)

    val x3 = x2 + dt * (v2 + (-(k*x2)*dt/2))
    val v3 = v2 + dt * (-double2real(k))* (x2 + v2*dt/2)

    val x4 = x3 + dt * (v3 + (-(k*x3)*dt/2))
    val v4 = v3 + dt * (-double2real(k))* (x3 + v3*dt/2)

    val x5 = x4 + dt * (v4 + (-(k*x4)*dt/2))
    val v5 = v4 + dt * (-double2real(k))* (x4 + v4*dt/2)

    val x6 = x5 + dt * (v5 + (-(k*x5)*dt/2))
    val v6 = v5 + dt * (-double2real(k))* (x5 + v5*dt/2)

    val x7 = x6 + dt * (v6 + (-(k*x6)*dt/2))
    val v7 = v6 + dt * (-double2real(k))* (x6 + v6*dt/2)
    
    val x8 = x7 + dt * (v7 + (-(k*x7)*dt/2))
    val v8 = v7 + dt * (-double2real(k))* (x7 + v7*dt/2)

    val x9 = x8 + dt * (v8 + (-(k*x8)*dt/2))
    val v9 = v8 + dt * (-double2real(k))* (x8 + v8*dt/2)

    val x10 = x9 + dt * (v9 + (-(k*x9)*dt/2))
    val v10 = v9 + dt * (-double2real(k))* (x9 + v9*dt/2)

    val x11 = x10 + dt * (v10 + (-(k*x10)*dt/2))
    val v11 = v10 + dt * (-double2real(k))* (x10 + v10*dt/2)

    val x12 = x11 + dt * (v11 + (-(k*x11)*dt/2))
    val v12 = v11 + dt * (-double2real(k))* (x11 + v11*dt/2)

    x12
  } 

  def rk2SpringUnrolled14(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    
    val x0 = x + dt * (v + (-(k*x)*dt/2))
    val v0 = v + dt * (-double2real(k))* (x + v*dt/2)

    val x1 = x0 + dt * (v0 + (-(k*x0)*dt/2))
    val v1 = v0 + dt * (-double2real(k))* (x0 + v0*dt/2)

    val x2 = x1 + dt * (v1 + (-(k*x1)*dt/2))
    val v2 = v1 + dt * (-double2real(k))* (x1 + v1*dt/2)

    val x3 = x2 + dt * (v2 + (-(k*x2)*dt/2))
    val v3 = v2 + dt * (-double2real(k))* (x2 + v2*dt/2)

    val x4 = x3 + dt * (v3 + (-(k*x3)*dt/2))
    val v4 = v3 + dt * (-double2real(k))* (x3 + v3*dt/2)

    val x5 = x4 + dt * (v4 + (-(k*x4)*dt/2))
    val v5 = v4 + dt * (-double2real(k))* (x4 + v4*dt/2)

    val x6 = x5 + dt * (v5 + (-(k*x5)*dt/2))
    val v6 = v5 + dt * (-double2real(k))* (x5 + v5*dt/2)

    val x7 = x6 + dt * (v6 + (-(k*x6)*dt/2))
    val v7 = v6 + dt * (-double2real(k))* (x6 + v6*dt/2)
    
    val x8 = x7 + dt * (v7 + (-(k*x7)*dt/2))
    val v8 = v7 + dt * (-double2real(k))* (x7 + v7*dt/2)

    val x9 = x8 + dt * (v8 + (-(k*x8)*dt/2))
    val v9 = v8 + dt * (-double2real(k))* (x8 + v8*dt/2)

    val x10 = x9 + dt * (v9 + (-(k*x9)*dt/2))
    val v10 = v9 + dt * (-double2real(k))* (x9 + v9*dt/2)

    val x11 = x10 + dt * (v10 + (-(k*x10)*dt/2))
    val v11 = v10 + dt * (-double2real(k))* (x10 + v10*dt/2)

    val x12 = x11 + dt * (v11 + (-(k*x11)*dt/2))
    val v12 = v11 + dt * (-double2real(k))* (x11 + v11*dt/2)

    val x13 = x12 + dt * (v12 + (-(k*x12)*dt/2))
    val v13 = v12 + dt * (-double2real(k))* (x12 + v12*dt/2)

    x13
  } 

  def rk2SpringUnrolled15(x: Real, v: Real): Real = {
    require(0.15 <= x && x <= 0.25 && 3.35 <= v && v <= 3.45)
      //(0.5 * x*x) + (0.5 * v*v) <= 0.5)

    val k = 2.3 // spring constant
    val dt = 0.1 // step size

    val x0 = x + dt * (v + (-(k*x)*dt/2))
    val v0 = v + dt * (-double2real(k))* (x + v*dt/2)

    val x1 = x0 + dt * (v0 + (-(k*x0)*dt/2))
    val v1 = v0 + dt * (-double2real(k))* (x0 + v0*dt/2)

    val x2 = x1 + dt * (v1 + (-(k*x1)*dt/2))
    val v2 = v1 + dt * (-double2real(k))* (x1 + v1*dt/2)

    val x3 = x2 + dt * (v2 + (-(k*x2)*dt/2))
    val v3 = v2 + dt * (-double2real(k))* (x2 + v2*dt/2)

    val x4 = x3 + dt * (v3 + (-(k*x3)*dt/2))
    val v4 = v3 + dt * (-double2real(k))* (x3 + v3*dt/2)

    val x5 = x4 + dt * (v4 + (-(k*x4)*dt/2))
    val v5 = v4 + dt * (-double2real(k))* (x4 + v4*dt/2)

    val x6 = x5 + dt * (v5 + (-(k*x5)*dt/2))
    val v6 = v5 + dt * (-double2real(k))* (x5 + v5*dt/2)

    val x7 = x6 + dt * (v6 + (-(k*x6)*dt/2))
    val v7 = v6 + dt * (-double2real(k))* (x6 + v6*dt/2)
    
    val x8 = x7 + dt * (v7 + (-(k*x7)*dt/2))
    val v8 = v7 + dt * (-double2real(k))* (x7 + v7*dt/2)

    val x9 = x8 + dt * (v8 + (-(k*x8)*dt/2))
    val v9 = v8 + dt * (-double2real(k))* (x8 + v8*dt/2)

    val x10 = x9 + dt * (v9 + (-(k*x9)*dt/2))
    val v10 = v9 + dt * (-double2real(k))* (x9 + v9*dt/2)

    val x11 = x10 + dt * (v10 + (-(k*x10)*dt/2))
    val v11 = v10 + dt * (-double2real(k))* (x10 + v10*dt/2)

    val x12 = x11 + dt * (v11 + (-(k*x11)*dt/2))
    val v12 = v11 + dt * (-double2real(k))* (x11 + v11*dt/2)

    val x13 = x12 + dt * (v12 + (-(k*x12)*dt/2))
    val v13 = v12 + dt * (-double2real(k))* (x12 + v12*dt/2)

    val x14 = x13 + dt * (v13 + (-(k*x13)*dt/2))
    val v14 = v13 + dt * (-double2real(k))* (x13 + v13*dt/2)
    x14
  }
}