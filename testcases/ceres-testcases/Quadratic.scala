
import leon.Real
import Real._


object Quadratic {


  def invariant(a: Real, b: Real, c: Real): Real = {
   // TODO: not sure this is the best way to write it
   // noise should maybe stay in the specs, and we introduce a new predicate
    noise(quadraticClassic(a, b, c)) >= noise(quadraticSmart(a, b, c))

  } holds

  /*
   var a = AffineFloat(2.999)
   var b = AffineFloat(56.0001)
   var c = AffineFloat(1.00074)  
  */
  def quadraticClassic(a: Real, b: Real, c: Real): (Real, Real) = {
    
    val discr = b*b - a * c * 4.0

    var r2 = (-b + sqrt(discr))/(a * 2.0)
    var r1 = (-b - sqrt(discr))/(a * 2.0)
    (r1, r2)
  } 

  def quadraticSmart(a: Real, b: Real, c: Real): (Real, Real) = {
   
    val (rk1, rk2) =
    if(b*b - a*c > 10.0) {
      if(b > 0.0) ((-b - sqrt(discr))/(a * 2.0), c * 2.0 /(-b - sqrt(discr)))
      else if(b < 0.0)  (c * 2.0 /(-b + sqrt(discr)), (-b + sqrt(discr))/(a * 2.0))
      else  ((-b - sqrt(discr))/(a * 2.0), (-b + sqrt(discr))/(a * 2.0))
    }
    else {
      ((-b - sqrt(discr))/(a * 2.0), (-b + sqrt(discr))/(a * 2.0))
    }

    (rk1, rk2)
  }



}
