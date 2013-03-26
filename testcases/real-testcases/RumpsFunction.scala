
object RumpsFunction {

  // In Ivancic's paper they use a = 77617, b= 33096
  def f(a: Double, b: Double) = (333.75 - a*a) * b*b*b*b*b*b +
    a*a*(11*a*a*b*b - 121.0*b*b*b*b - 2.0) + 5.5*b*b*b*b*b*b*b*b + a/(2*b)

}
