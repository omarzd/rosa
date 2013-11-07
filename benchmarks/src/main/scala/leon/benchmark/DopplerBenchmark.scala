package leon
package benchmark

import annotation.tailrec
import com.google.caliper.Param

import scala.util.Random._

import ceres.common.{DoubleDouble, QuadDouble}

// a caliper benchmark is a class that extends com.google.caliper.Benchmark
// the SimpleScalaBenchmark trait does it and also adds some convenience functionality
class DopplerBenchmark extends SimpleScalaBenchmark with Utils {

  @Param(Array("10", "100", "1000", "10000"))
  val length: Int = 0
  
  var inputsFloat: Array[(Float, Float, Float)] = _
  var inputsDouble: Array[(Double, Double, Double)] = _
  var inputsDDouble: Array[(DoubleDouble, DoubleDouble, DoubleDouble)] = _
  var inputsQDouble: Array[(QuadDouble, QuadDouble, QuadDouble)] = _
  
  //var inputsFixedInt: Array[(Int, Int, Int)] = _ 16 bit is not possible
  var inputsFixedLong: Array[(Long, Long, Long)] = _

  override def setUp() {
    def getRandomU: Float = -100f + nextFloat * 200.0f
    def getRandomV: Float = -20f + nextFloat * 19980.0f
    def getRandomT: Float = -30f + nextFloat * 80.0f
      
    inputsFloat = Array.fill(length) { (getRandomU, getRandomV, getRandomT) }
    inputsDouble = inputsFloat.map(i => (i._1.toDouble, i._2.toDouble, i._3.toDouble))
    inputsDDouble = inputsDouble.map(i => (DoubleDouble(i._1), DoubleDouble(i._2), DoubleDouble(i._3)))
    inputsQDouble = inputsFloat.map(i => (QuadDouble(i._1), QuadDouble(i._2), QuadDouble(i._3)))

    inputsFixedLong = inputsFloat.map(i => (floatToLong(i._1, 24), floatToLong(i._2, 16), floatToLong(i._3,25)))
  }
  
  def timeFloat(reps: Int) = repeat(reps) {
    var result = 0.0f
    inputsFloat.foreach { x => 
      result += doppler1Float(x._1, x._2, x._3)
    }
    result
  }

  def timeDouble(reps: Int) = repeat(reps) {
    var result = 0.0f
    inputsFloat.foreach { x => 
      result += doppler1Float(x._1, x._2, x._3)
    }
    result
  }

  def timeDoubleDouble(reps: Int) = repeat(reps) {
    var result = DoubleDouble(0.0)
    inputsDDouble.foreach { x => 
      result += doppler1DDouble(x._1, x._2, x._3)
    }
    result
  }

  def timeQuadDouble(reps: Int) = repeat(reps) {
    var result = QuadDouble(0.0)
    inputsQDouble.foreach { x => 
      result += doppler1QDouble(x._1, x._2, x._3)
    }
    result
  }

  def timeFixedLong(reps: Int) = repeat(reps) {
    var result = 0l
    inputsFixedLong.foreach { x => 
      result += doppler1FixedLong(x._1, x._2, x._3)
    }
    result
  }

  def doppler1Float(u: Float, v: Float, T: Float): Float = {
    val t1 = 331.4f + 0.6f * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))
  }

  def doppler1Double(u: Double, v: Double, T: Double): Double = {
    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))
  }

  def doppler1DDouble(u: DoubleDouble, v: DoubleDouble, T: DoubleDouble): DoubleDouble = {
    import DoubleDouble._
    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))
  }

  def doppler1QDouble(u: QuadDouble, v: QuadDouble, T: QuadDouble): QuadDouble = {
    import QuadDouble._
    val t1 = 331.4 + 0.6 * T
    (- (t1) *v) / ((t1 + u)*(t1 + u))
  }

  //u -> <1,32,24>v -> <1,32,16>#T -> <1,32,25>
  def doppler1FixedLong(u : Long, v : Long, T : Long) : Long = {
    val tmp1 = (1288490189l * T) >> 30l
    val tmp2 = ((1389992346l << 4l) + tmp1) >> 4l
    val t1 = tmp2
    val tmp3 = -(t1)
    val tmp4 = (tmp3 * v) >> 30l
    val tmp5 = ((t1 << 2l) + u) >> 2l
    val tmp6 = ((t1 << 2l) + u) >> 2l
    val tmp7 = (tmp5 * tmp6) >> 31l
    val tmp8 = (tmp4 << 28l) / tmp7
    tmp8
  }

}