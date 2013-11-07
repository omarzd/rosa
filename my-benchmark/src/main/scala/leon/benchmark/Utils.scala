package leon
package benchmark

trait Utils {

  def floatToLong(d: Float, f: Int): Long = (d * math.pow(2, f)).round.toLong
  def floatToInt(d: Float, f: Int): Int = (d * math.pow(2, f)).round.toInt
  def longToDouble(i: Long, f: Int): Double = i.toDouble / math.pow(2, f)

}