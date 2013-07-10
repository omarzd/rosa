
import leon.Real
import Real._


object InitialExample {

  def mainFunction(a: Real, b: Real, c: Real): Real = {
    require(a.in(1.0, 9.0) && 4.0 <= b && b <= 4.0 && 5.0 <= c && c <= 5.0 &&
      a + b > c + 0.1 && a + c > b + 0.0001 && b + c > a + 0.1 &&
      a < c && b < c && a +/- 1e-13)
    
    val area = triangleSorted(a, b, c)
    area
  } ensuring(res => res +/- 1e-11)


  
  def triangleSorted(a: Real, b: Real, c: Real): Real = {
    require(a < c && b < c)
    
    val discr =
      if (a < b) {
        (c+(b+a)) * (a-(c-b)) * (a+(c-b)) * (c+(b-a))
      } else {
        (c+(a+b)) * (b-(c-a)) * (b+(c-a)) * (c+(a-b))      
      }
    sqrt(discr) / 4.0
  }
}
