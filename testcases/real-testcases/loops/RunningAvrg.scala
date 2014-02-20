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

  // standard deviation and variance as a running computation
  // weighted mean

  // inner product (this we'd have to compare against the specialized work)


  // online kurtosis algorithm
  //http://en.wikipedia.org/wiki/Algorithms_for_calculating_variance

  // a possible challenge: computing a two-pass covariance
  //http://en.wikipedia.org/wiki/Algorithms_for_calculating_variance
  // the first sum will have already some error
}