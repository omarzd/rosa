import leon.Real
import Real._

// Tests if-then-else handling
object IfThenElseSqrt1 {

  
   def squareRoot3(x: Real): Real = {
    require( x >< (0,10) && x +/- 1e-10 )
    if (x < 1e-5)
      1 + 0.5 * x
    else
      sqrt(1 + x)
  } ensuring( res => res +/- 1e-10)

}