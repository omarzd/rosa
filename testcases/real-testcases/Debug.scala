


object Debug {

  def bspline0(u: Double): Double = {
    require(0 <= u && u <= 1)
    (1 - u) * (1 - u) * (1 - u) * (1.0/6.0)
  } ensuring (res => res >= -56020.0)

  
  
}
