
import leon.Real
import Real._


object Quadratic {

  def quadraticClassicRoot1(a: Real, b: Real, c: Real): Real = {
    require(a.in(2.5, 3.5) && b.in(54.0, 57.0) && c.in(0.5, 1.5))
    val discr = b*b - a * c * 4.0

    (-b - sqrt(discr))/(a * 2.0)
  } ensuring (res => noise(res, 1e-13))

  def quadraticClassicRoot2(a: Real, b: Real, c: Real): Real = {
    require(a.in(2.5, 3.5) && b.in(54.0, 57.0) && c.in(0.5, 1.5))
    val discr = b*b - a * c * 4.0

    (-b + sqrt(discr))/(a * 2.0)
  } ensuring (res => noise(res, 1e-13))


  def quadraticSmartRoot1(a: Real, b: Real, c: Real): Real = {
    require(a.in(2.5, 3.5) && b.in(54.0, 57.0) && c.in(0.5, 1.5))

    val discr = b*b - a * c * 4.0

    if(b*b - a*c > 10.0) {
      if(b > 0.0) (-b - sqrt(discr))/(a * 2.0)
      else if(b < 0.0)  c * 2.0 /(-b + sqrt(discr))
      else  (-b - sqrt(discr))/(a * 2.0)
    }
    else {
      (-b - sqrt(discr))/(a * 2.0)
    }

  } ensuring (res => noise(res, 1e-13))
  

  def quadraticSmartRoot2(a: Real, b: Real, c: Real): Real = {
    require(a.in(2.5, 3.5) && b.in(54.0, 57.0) && c.in(0.5, 1.5))

    val discr = b*b - a * c * 4.0

    if(b*b - a*c > 10.0) {
      if(b > 0.0) c * 2.0 /(-b - sqrt(discr))
      else if(b < 0.0)  (-b + sqrt(discr))/(a * 2.0)
      else (-b + sqrt(discr))/(a * 2.0)
    }
    else {
      (-b + sqrt(discr))/(a * 2.0)
    }
  } ensuring (res => noise(res, 1e-13))
  
  /*def quadraticClassic(a: Real, b: Real, c: Real): (Real, Real) = {
    require(a.in(2.5, 3.5) && b.in(54.0, 57.0) && c.in(0.5, 1.5))
    val discr = b*b - a * c * 4.0

    var r2 = (-b + sqrt(discr))/(a * 2.0)
    var r1 = (-b - sqrt(discr))/(a * 2.0)
    (r1, r2)
  } ensuring (res => noise(res._1, 1e-13) && noise(res._2, 1e-13))

  def quadraticSmart(a: Real, b: Real, c: Real): (Real, Real) = {
    require(a.in(2.5, 3.5) && b.in(54.0, 57.0) && c.in(0.5, 1.5))

    val discr = b*b - a * c * 4.0

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
  } ensuring (res => noise(res._1, 1e-13) && noise(res._2, 1e-13))
  */

  /*def invariant(a: Real, b: Real, c: Real): Real = {
   // TODO: not sure this is the best way to write it
   // noise should maybe stay in the specs, and we introduce a new predicate
    noise(quadraticClassic(a, b, c)) >= noise(quadraticSmart(a, b, c))
  } holds
  */
}
