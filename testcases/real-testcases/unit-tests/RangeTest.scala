import leon.Real
import Real._


object RangeTest {

  def withIn(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    x + y
  }

  def comparisons(x: Real, y: Real): Real = {
    require(-2.2 <= x && x <= 2.3 && 3.5 <= y && y <= 7.5)
    x + y
  }

  // Buggy
  // doesn't parse (correctly)
  /*def invalidInterval(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    x + y
  }*/

  
  def invalidIntervalComparisons(x: Real, y: Real): Real = {
    require(-2.2 <= x && x <= -2.3 && 3.5 <= y && y <= 7.5)
    x + y
  }

  def unBounded(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3))
    x + y
  }

  def unBounded2(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y <= 3.3)
    x + y
  }
}