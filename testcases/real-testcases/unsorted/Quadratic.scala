
import leon.Real
import Real._
import leon.Utils._

object Quadratic {

  /* ---------------------
        Tight bounds.
  ------------------------- */
  def classicRoot1(a: Real, b: Real, c: Real): Real = {
    require(a.in(2.5, 3.5) && b.in(54.0, 57.0) && c.in(0.5, 1.5))
    val discr = b*b - a * c * 4.0
    (-b - sqrt(discr))/(a * 2.0)
  } ensuring (res => noise(res, 1e-13))

  def classicRoot2(a: Real, b: Real, c: Real): Real = {
    require(a.in(2.5, 3.5) && b.in(54.0, 57.0) && c.in(0.5, 1.5))
    val discr = b*b - a * c * 4.0
    (-b + sqrt(discr))/(a * 2.0)
  } ensuring (res => noise(res, 1e-13))

  def smartRoot1(a: Real, b: Real, c: Real): Real = {
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
  

  def smartRoot2(a: Real, b: Real, c: Real): Real = {
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
  
  def tightInvariant1(a: Real, b: Real, c: Real): Boolean = {
    require(a.in(2.5, 3.5) && b.in(54.0, 57.0) && c.in(0.5, 1.5))

    val c1 = classicRoot1(a, b, c)
    val s1 = smartRoot1(a, b, c)
    s1 <= c1 + 0.001
  } holds

  def tightInvariant2(a: Real, b: Real, c: Real): Boolean = {
    require(a.in(2.5, 3.5) && b.in(54.0, 57.0) && c.in(0.5, 1.5))

    val c2 = classicRoot2(a, b, c)
    val s2 = smartRoot2(a, b, c)
    ~s2 <= ~c2 + 1e-13
  } holds

  /* ---------------------
        More general bounds.
  ------------------------- */
  def classicRoot1General(a: Real, b: Real, c: Real): Real = {
    require(a.in(1.0, 7.0) && b.in(20.0, 60.0) && c.in(-5.0, 7.5) &&
      b*b - a * c * 4.0 > 0.1)
    val discr = b*b - a * c * 4.0
    (-b - sqrt(discr))/(a * 2.0)
  } ensuring (res => noise(res, 1e-13))

  def classicRoot2General(a: Real, b: Real, c: Real): Real = {
    require(a.in(1.0, 7.0) && b.in(20.0, 60.0) && c.in(-5.0, 7.5) &&
      b*b - a * c * 4.0 > 0.1)
    val discr = b*b - a * c * 4.0
    (-b + sqrt(discr))/(a * 2.0)
  } ensuring (res => noise(res, 1e-13))

  def smartRoot1General(a: Real, b: Real, c: Real): Real = {
    require(a.in(1.0, 7.0) && b.in(20.0, 60.0) && c.in(-5.0, 7.5) &&
      b*b - a * c * 4.0 > 0.1)

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
  
  def smartRoot2General(a: Real, b: Real, c: Real): Real = {
    require(a.in(1.0, 7.0) && b.in(20.0, 60.0) && c.in(-5.0, 7.5) &&
      b*b - a * c * 4.0 > 0.1)

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

  def generalInvariant1(a: Real, b: Real, c: Real): Boolean = {
    require(a.in(1.0, 7.0) && b.in(20.0, 60.0) && c.in(-5.0, 7.5) &&
      b*b - a * c * 4.0 > 0.1)

    val c1 = classicRoot1General(a, b, c)
    val s1 = smartRoot1General(a, b, c)
    //s1 == c1 + 0.001
    s1 <= c1 + 0.001
  } holds

  def generalInvariant2(a: Real, b: Real, c: Real): Boolean = {
    require(a.in(1.0, 7.0) && b.in(20.0, 60.0) && c.in(-5.0, 7.5) &&
      b*b - a * c * 4.0 > 0.1)

    val c2 = classicRoot2General(a, b, c)
    val s2 = smartRoot2General(a, b, c)
    //s2 == c2 + 0.001
    s2 <= c2 + 0.001
  } holds
  
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
