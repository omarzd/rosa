import leon.real._
import RealOps._
import annotations._


object Quadratic {

  def quadratic(a: Real, b: Real, c: Real): (Real, Real) = {
    require(1 < a && a < 60 && 1 < b && b < 60 && 1 < c && c < 60 &&
      b*b - a * c * 4.0 > 1e-6)

    val discr = b*b - a * c * 4.0
    val r2 = (-b + sqrt(discr))/(a * 2.0)
    val r1 = (-b - sqrt(discr))/(a * 2.0)
    (r1, r2)
  }

  @robust
  def quadraticSmart(a: Real, b: Real, c: Real): (Real, Real) = {
    require(1 < a && a < 60 && 1 < b && b < 60 && 1 < c && c < 60 &&
      b*b - a * c * 4.0 > 1e-6)

    val discr = b*b - a * c * 4.0
    
    if(b*b - a*c > 10.0) {  
      if(b > 0.0) 
        ((-b - sqrt(discr))/(a * 2.0), c * 2.0 /(-b - sqrt(discr)))
      else if(b < 0.0)  
        (c * 2.0 /(-b + sqrt(discr)), (-b + sqrt(discr))/(a * 2.0))
      else  
        ((-b - sqrt(discr))/(a * 2.0), (-b + sqrt(discr))/(a * 2.0))
    }
    else
      ((-b - sqrt(discr))/(a * 2.0), (-b + sqrt(discr))/(a * 2.0))
  
    }

}