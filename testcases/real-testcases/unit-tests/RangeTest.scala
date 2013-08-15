import leon.Real
import Real._


object ParsingTest {

  def noise(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    x + y
  } ensuring(res => res >< (0, 4))

  def noise(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    x + y
  } ensuring(res => res >< (0, 4))


  

  def actual(x: Real, y: Real): Real = {
    require(x >< (-2.2, 2.3) && y >< (3.5, 7.5))
    x * x
  } ensuring(-0.05 <= ~res._1 && ~res._1 <= 0.17)


  // Buggy
  def noiseBug(x: Real, y: Real): Real = {
    require(x >< (-2.2, -2.3) && y >< (3.5, 7.5))
    x + y
  } ensuring(res => res < 0)

  def noiseBug(x: Real, y: Real): Real = {
    require(x >< (-2.2, -2.3) && y >< (3.5, 7.5))
    x + y
  } ensuring(res => res >< (0, 4))

  def unBounded(x: Real, y: Real): Real = {
    require(x >< (-2.2, -2.3))
    x + y
  } ensuring(res => res < 0)

  def unBounded2(x: Real, y: Real): Real = {
    require(x >< (-2.2, -2.3) && y <= 3.3)
    x + y
  } ensuring(res => res < 0)

}