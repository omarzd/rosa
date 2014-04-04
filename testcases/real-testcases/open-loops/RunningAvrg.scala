import leon.Real
import Real._

object RunningAvrg {


  def loopInvariant(m: Real, x: Real, c: Real): Real = {
    require(-1200 <= m && currMean <= 1200 && -1200 <= m && currMean <= 1200 &&
        1 <= c <= 10)


  } ensuring ( res => 
    )


  @modelInput                                 // this roundoff thing is probably not going to compile
  def nextValue: Real = { ??? } ensuring (res => -1200 <= next && next <= 1200 && roundoff(res))

  /**
    The challenge in this example is that it uses the loop counter
    in the computation. We may still be able to prove something,
    since this computation has to hold for any counter.
  */
  def mean(currMean: Real, counter: Int): Real = {
    require(-1200 <= currMean && currMean <= 1200 && loopCounter(counter))

    if (counter < 100) {
      val nextVal = nextValue
      val newMean = ((counter.toReal - 1) * currMean + nextValue) / counter.toReal
      mean(newMean, counter + 1)
    } else {
      currMean
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