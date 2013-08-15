import leon.Real
import Real._


object ParsingTest {

  def realFunction(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    x * x
  }

  def arithmetic(x: Real, y: Real): Real = {
    require(-2.2 <= x && x <= 2.3 && 3.5 <= y && y <= 7.5) 
    x * (sqrt(x) - y) / x + (-x)
  }

  def noise(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5) && x +/- 1e-9 && y +/- 1e-5)
    x + y
    // TODO: doesn't parse
  } //ensuring(res => res >< (0.0, 4.0) && res +/- 1e-3)

  def actual(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    x * x
    // TODO: doesn't parse
  } //ensuring(res => ~res >< (0.0, 4.0))

  def assertion(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    val z = x * x
    assert(~z <= 7.0 && z +/- 1e-9)
    val z2 = z * z
    z2
  } ensuring(res => res <= 4 && 0 <= res)

  def ifThenElse(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    if(x * x <= 0 && y <= 5.4) {
      x * x + y
    } else {
      x / y
    }
  } ensuring(res => ~res <= 4 && 0 <= ~res)

  def ifThenElse2(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    val z = if(x * x <= 0 && y <= 5.4) {
      x * x + y
    } else {
      x / y
    }
    z * z
  }

  def functionCall(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    realFunction(x * x, y * y)
  }
  
  
  // Errors we should catch
  def ints(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    x * x + (3 + 4)
  }

  /*def actualBug(x: Real, y: Real): Real = {
    // TODO: doesn't parse
    require(~x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    x * x
  } ensuring(res => ~res >< (0, 4))
  */
}