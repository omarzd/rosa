


object Debug {

  def matyas(x: Double, y: Double): Double  = {
    require(-9 <= x && x <= -5 && 1 <= y && y <= 3)
    0.26*(x*x + y*y) - 0.48*x*y
  } ensuring (res => res >= -56020.0)


  
}
