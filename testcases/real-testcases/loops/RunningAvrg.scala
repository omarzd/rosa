import leon.Real
import Real._

object RunningAvrg {

  def mean(sum: Real, x: RealList, counter: Real): Real = {
    require(-1200 <= sum && sum <= 1200 && -1200 <= x && x <= 1200 &&
            counter isInteger)

    if (counter < MAX) {
      mean( ((counter - 1) * sum + x.next) / counter, x, counter + 1)
    } else {
      sum
    }
    
  } ensuring ( res => res <= 1200.0 && -1200.0 <= res)

}