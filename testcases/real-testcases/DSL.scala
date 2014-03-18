import leon.real._
import RealOps._


object DSL {

  def sine(x: Real): Real = {
    // is translated on the front-end into (x > -1.57079632679 && x < 1.57079632679)
    require( x ∈ (-1.57079632679, 1.57079632679) )
    
    // x°3 is translated on the front-end into (x*x)*x
    x - x°°3/6.0 + x°5/120.0 + x°7/5040.0

    // translated on the front-end to (~res <= 0.99 && ~res >= -0.99)
  } ensuring( ~_ ∈= (-0.99, 0.99) )
  

  
  def verhulst(r: Real, K: Real, x: Real): Real = {
    // ± is going to need parentheses once we have more than constants, due to precedence
    require( r == 4.0 && K == 1.11 && x ∈ (0.1, 0.3) && r ± 0.001 && K ± 1e-5 && x ± 1e-6 )
    
    (r*x) / (1 + (x/K))

  } ensuring ( _ <= 1.2 )

}