

object DoubleFun {

  def literal(): Double = 4.5

  def arithmetic(x: Double, y: Double, z: Double): Double = {
    x * y + z / (y - x) * (-x) + 4.5
  } ensuring (res => res > 0)

  def ifThenElse(x: Double, y: Double, z: Double): Double = {
    val s = (x + y + z) / 2.0

    if (s > 10.0) {
      s * (s - x) * (s - y) * (s - z)
    } else {
      ((x+(y+z)) * (z-(x-y)) * (z+(x-y)) * (x+(y-z))) / 4.0
    }
  } ensuring (res => res > 0)
}
