package leon
package benchmark

import annotation.tailrec
import com.google.caliper.Param

import scala.util.Random._

import ceres.common.{DoubleDouble, QuadDouble}

// a caliper benchmark is a class that extends com.google.caliper.Benchmark
// the SimpleScalaBenchmark trait does it and also adds some convenience functionality
class TurbineBenchmark extends SimpleScalaBenchmark with Utils {

  @Param(Array("10", "100", "1000", "10000"))
  val length: Int = 0
  
  var inputsFloat: Array[(Float, Float, Float)] = _
  var inputsDouble: Array[(Double, Double, Double)] = _
  var inputsDDouble: Array[(DoubleDouble, DoubleDouble, DoubleDouble)] = _
  var inputsQDouble: Array[(QuadDouble, QuadDouble, QuadDouble)] = _
  
  var inputsFixedInt: Array[(Int, Int, Int)] = _
  var inputsFixedLong: Array[(Long, Long, Long)] = _

  override def setUp() { //require(v >< (-4.5, -0.3) && w >< (0.4, 0.9) && r >< (3.8, 7.8))
    def getRandomV: Float = -4.5f + nextFloat * 4.2f
    def getRandomW: Float = 0.4f + nextFloat * 0.5f
    def getRandomR: Float = 3.8f + nextFloat * 4.0f
      
    inputsFloat = Array.fill(length) { (getRandomV, getRandomW, getRandomR) }
    inputsDouble = inputsFloat.map(i => (i._1.toDouble, i._2.toDouble, i._3.toDouble))
    inputsDDouble = inputsDouble.map(i => (DoubleDouble(i._1), DoubleDouble(i._2), DoubleDouble(i._3)))
    inputsQDouble = inputsFloat.map(i => (QuadDouble(i._1), QuadDouble(i._2), QuadDouble(i._3)))

    //formats: #v -> <1,16,12>, #w -> <1,16,15>,  #r -> <1,16,12>, 
    inputsFixedInt = inputsFloat.map(i => (floatToInt(i._1, 12), floatToInt(i._2, 15), floatToInt(i._3,12)))
    //formats: #v -> <1,32,28>, #w -> <1,32,31>,  #r -> <1,32,28>,  )
    inputsFixedLong = inputsFloat.map(i => (floatToLong(i._1, 28), floatToLong(i._2, 31), floatToLong(i._3,28)))
  }
  
  def timeFloat(reps: Int) = repeat(reps) {
    var result = 0.0f
    inputsFloat.foreach { x => 
      result += turbineFloat(x._1, x._2, x._3)
    }
    result
  }

  def timeDouble(reps: Int) = repeat(reps) {
    var result = 0.0f
    inputsFloat.foreach { x => 
      result += turbineFloat(x._1, x._2, x._3)
    }
    result
  }

  def timeDoubleDouble(reps: Int) = repeat(reps) {
    var result = DoubleDouble(0.0)
    inputsDDouble.foreach { x => 
      result += turbineDDouble(x._1, x._2, x._3)
    }
    result
  }

  def timeQuadDouble(reps: Int) = repeat(reps) {
    var result = QuadDouble(0.0)
    inputsQDouble.foreach { x => 
      result += turbineQDouble(x._1, x._2, x._3)
    }
    result
  }

  def timeFixedInt(reps: Int) = repeat(reps) {
    var result = 0
    inputsFixedInt.foreach { x => 
      result += turbineFixedInt(x._1, x._2, x._3)
    }
    result
  }

  def timeFixedLong(reps: Int) = repeat(reps) {
    var result = 0l
    inputsFixedLong.foreach { x => 
      result += turbineFixedLong(x._1, x._2, x._3)
    }
    result
  }

  def turbineFloat(v: Float, w: Float, r: Float): Float = {
    3 + 2/(r*r) - 0.125f*(3-2*v)*(w*w*r*r)/(1-v) - 4.5f
  }

  def turbineDouble(v: Double, w: Double, r: Double): Double = {
    3 + 2/(r*r) - 0.125*(3-2*v)*(w*w*r*r)/(1-v) - 4.5
  }

  def turbineDDouble(v: DoubleDouble, w: DoubleDouble, r: DoubleDouble): DoubleDouble = {
    import DoubleDouble._
    3 + 2/(r*r) - 0.125*(3-2*v)*(w*w*r*r)/(1-v) - 4.5
  }

  def turbineQDouble(v: QuadDouble, w: QuadDouble, r: QuadDouble): QuadDouble = {
    import QuadDouble._
    3 + 2/(r*r) - 0.125*(3-2*v)*(w*w*r*r)/(1-v) - 4.5
  }

  def turbineFixedInt(v: Int, w: Int, r: Int): Int = {
    val tmp1 = (r * r) >> 15
    val tmp2 = (16384 << 11) / tmp1
    val tmp3 = ((24576 << 2) + tmp2) >> 2
    val tmp4 = (16384 * v) >> 14
    val tmp5 = (24576 - (tmp4 << 2)) >> 2
    val tmp6 = (16384 * tmp5) >> 14
    val tmp7 = (w * w) >> 15
    val tmp8 = (tmp7 * r) >> 15
    val tmp9 = (tmp8 * r) >> 15
    val tmp10 = (tmp6 * tmp9) >> 15
    val tmp11 = (16384 - (v << 2)) >> 2
    val tmp12 = (tmp10 << 14) / tmp11
    val tmp13 = (tmp3 - (tmp12 << 3)) >> 2
    val tmp14 = ((tmp13 << 1) - 18432) >> 2
    tmp14
  }

  def turbineFixedLong(v : Long, w : Long, r : Long) : Long = {
    val tmp1 = (r * r) >> 31
    val tmp2 = (1073741824 << 27) / tmp1
    val tmp3 = ((1610612736 << 2) + tmp2) >> 2
    val tmp4 = (1073741824 * v) >> 30
    val tmp5 = (1610612736 - (tmp4 << 2)) >> 2    
    val tmp6 = (1073741824 * tmp5) >> 30
    val tmp7 = (w * w) >> 31
    val tmp8 = (tmp7 * r) >> 31
    val tmp9 = (tmp8 * r) >> 31
    val tmp10 = (tmp6 * tmp9) >> 31
    val tmp11 = (1073741824 - (v << 2)) >> 2
    val tmp12 = (tmp10 << 30) / tmp11
    val tmp13 = (tmp3 - (tmp12 << 3)) >> 2
    val tmp14 = ((tmp13 << 1) - 1207959552) >> 2
    tmp14
  }

}

