import leon.NumericUtils._


object DoubleFun {

  def wrongSignature1(x: Double, y: Double): Boolean = {
    require(x >= -5 && x <= 5 && y >= -5 && y <= 5)
    if (x * y < 7.0) true
    else false
  } ensuring (res => res)

  def wrongSignature2(x: Boolean, y: Double): Double = {
    require(y >= -5 && y <= 5)
    if (x) y*y
    else y*y*y
  } ensuring (res => (res > 0 && absRoundoff(res) <= 1e-10))

  def noPost(x: Double, y: Double): Double = {
    require(x >= -5 && x <= 5 && y >= -5 && y <= 5)
    (x + y) * x * y
  }

  def noPre(x: Double, y: Double): Double = {
    (x + y) * x * y
  } ensuring (res => (res > 0 && absRoundoff(res) <= 1e-10))


  def arithmeticFull(x: Double, y: Double, z: Double): Double = {
    require(x >= -5 && x <= 5 && y >= -5 && y <= 5 && z >= -5 && z <= 5)
    x * y + z / (y - x) * (-x) + 4.5
  } ensuring (res => (absRoundoff(res) <= 1e-7 && res <= 30.4))

  // Should be handled with inlining
  def arithmeticWithVal(x: Double, y: Double): Double = {
    require(x >= -5 && x <= 5 && y >= -5 && y <= 5)
    val temp = x * y
    temp * temp
  } ensuring (res => (absRoundoff(res) <= 1e-7 && res <= 30.4))

  def ifThenElse(x: Double, y: Double, z: Double): Double = {
    require(x >= -5 && x <= 5 && y >= -5 && y <= 5 && z >= -5 && z <= 5)

    if (x > 10.0) {
      (z - x) * (x - y) * (y - z)
    } else {
      ((x+(y+z)) * (z-(x-y)) * (z+(x-y)) * (x+(y-z)))
    }
  } ensuring (res => (res > 0 && absRoundoff(res) <= 1e-10))
 
  def ifThenElseWithVal(x: Double, y: Double, z: Double): Double = {
    require(x >= -5 && x <= 5 && y >= -5 && y <= 5 && z >= -5 && z <= 5)
    val s = (x + y + z) / 2.0

    if (s > 10.0) {
      s * (s - x) * (s - y) * (s - z)
    } else {
      ((x+(y+z)) * (z-(x-y)) * (z+(x-y)) * (x+(y-z))) / 4.0
    }
  } ensuring (res => (res > 0 && absRoundoff(res) <= 1e-10))
  
}
