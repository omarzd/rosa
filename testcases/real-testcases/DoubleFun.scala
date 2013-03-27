import leon.NumericUtils._


object DoubleFun {

  //def literal(): Double = 4.5

  def arithmetic(x: Double, y: Double, z: Double): Double = {
    require(x >= -5 && x <= 5 && y >= -5 && y <= 5 && z >= -5 && z <= 5)
    val err = absRoundoff(3.5)
    x * y + z / (y - x) * (-x) + 4.5
  } ensuring (res => (absRoundoff(res) <= 1e-7 && res <= 3.4))

  /*def ifThenElse(x: Double, y: Double, z: Double): Double = {
    require(x >= -5 && x <= 5 && y >= -5 && y <= 5 && z >= -5 && z <= 5)
    val s = (x + y + z) / 2.0

    if (s > 10.0) {
      s * (s - x) * (s - y) * (s - z)
    } else {
      ((x+(y+z)) * (z-(x-y)) * (z+(x-y)) * (x+(y-z))) / 4.0
    }
  } ensuring (res => (res > 0 && absRoundoff(res) <= 1e-10))
  */
}
