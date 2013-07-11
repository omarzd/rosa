import leon.Real
import Real._

import leon.Utils._

//http://www.coranac.com/2009/07/sines/
object SineApproximations {

  def sineOrder3(x: Real): Real = {
    require(x.in(-2.0, 2.0))
    0.954929658551372 * x -  0.12900613773279798*(x*x*x)
  } ensuring(res => -1.0 < res && res < 1.0 && res +/- 1e-14)

}