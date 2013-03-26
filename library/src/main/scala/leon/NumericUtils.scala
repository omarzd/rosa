package leon


object NumericUtils {
  
  def absRoundoff(d: Double): Double = math.pow(2, -53) * d

  // TODO
  //def relRoundoff(d: Double): Double = math.pow(2, -53)

  // TODO: better notation for intervals
  // x in <-5, 5>  for instance could work
}
