import leon.real._
import RealOps._


object StraightlineWithError {

   def dopplerRefactoredWithError(u: Real, v: Real, T: Real): Real = {
    require(-100.0 <= u && u <= 100 && 20 <= v && v <= 20000 && -30 <= T && T <= 50 &&
        u +/- 1e-11 && v +/- 1e-11 && T +/- 1e-11)
    
    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))

  }

  /*def rigidBodyWithError(x1: Real, x2: Real, x3: Real): Real = {
    require(-15.0 <= x1 && x1 <= 15 && -15.0 <= x2 && x2 <= 15.0 &&
      -15.0 <= x3 && x3 <= 15 && x1 +/- 1e-11 && x2 +/- 1e-11 && x3 +/- 1e-11)

    2*(x1*x2*x3) + (3*x3*x3) - x2*(x1*x2*x3) + (3*x3*x3) - x2
  }*/


  def jetEngineRefactoredWithError(x1: Real, x2: Real): Real = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5 &&
      x1 +/- 1e-11 && x2 +/- 1e-11)

    val t = (3*x1*x1 + 2*x2 - x1)

    x1 + ((2*x1*(t/(x1*x1 + 1))*
    (t/(x1*x1 + 1) - 3) + x1*x1*(4*(t/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(t/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  }

  def turbine1RefactoredWithError(v: Real, w: Real, r: Real): Real = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8 &&
      v +/- 1e-11 && w +/- 1e-11 && r +/- 1e-11)

    val t = w*w*r*r

    3 + 2/(r*r) - 0.125*(3-2*v)*(t)/(1-v) - 4.5
    
  }

  def turbine2RefactoredWithError(v: Real, w: Real, r: Real): Real = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8 &&
      v +/- 1e-11 && w +/- 1e-11 && r +/- 1e-11)

    val t = w*w*r*r
    6*v - 0.5 * v * (t) / (1-v) - 2.5
    
  }

  def turbine3RefactoredWithError(v: Real, w: Real, r: Real): Real = {
    require(-4.5 <= v && v <= -0.3 && 0.4 <= w && w <= 0.9 && 3.8 <= r && r <= 7.8 &&
      v +/- 1e-11 && w +/- 1e-11 && r +/- 1e-11)

    val t = w*w*r*r
    3 - 2/(r*r) - 0.125 * (1+2*v) * (t) / (1-v) - 0.5
    
  }


}