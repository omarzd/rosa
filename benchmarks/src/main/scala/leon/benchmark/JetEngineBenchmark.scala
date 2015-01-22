package leon
package benchmark

import annotation.tailrec
import com.google.caliper.Param

import scala.util.Random._

import ceres.common.{DoubleDouble, QuadDouble}

// a caliper benchmark is a class that extends com.google.caliper.Benchmark
// the SimpleScalaBenchmark trait does it and also adds some convenience functionality
class JetEngineBenchmark extends SimpleScalaBenchmark with Utils {

  @Param(Array("10", "100", "1000", "10000"))
  val length: Int = 0
  
  var inputsFloat: Array[(Float, Float)] = _
  var inputsDouble: Array[(Double, Double)] = _
  var inputsDDouble: Array[(DoubleDouble, DoubleDouble)] = _
  var inputsQDouble: Array[(QuadDouble, QuadDouble)] = _
  
  //var inputsFixedInt: Array[(Int, Int, Int)] = _ 16 bit is not possible
  var inputsFixedLong: Array[(Long, Long)] = _

  override def setUp() { //require(x1 >< (-5, 5) && x2 >< (-20, 5))
    def getRandomX1: Float = -5f + nextFloat * 10.0f
    def getRandomX2: Float = -20f + nextFloat * 25.0f
      
    inputsFloat = Array.fill(length) { (getRandomX1, getRandomX2) }
    inputsDouble = inputsFloat.map(i => (i._1.toDouble, i._2.toDouble))
    inputsDDouble = inputsDouble.map(i => (DoubleDouble(i._1), DoubleDouble(i._2)))
    inputsQDouble = inputsFloat.map(i => (QuadDouble(i._1), QuadDouble(i._2)))


  //formats: Map(#x2 -> <1,32,26> #x1 -> <1,32,28>,
    inputsFixedLong = inputsFloat.map(i => (floatToLong(i._1, 28), floatToLong(i._2, 26)))
  }
  
  def timeFloat(reps: Int) = repeat(reps) {
    var result = 0.0f
    inputsFloat.foreach { x => 
      result += jetFloat(x._1, x._2)
    }
    result
  }

  def timeDouble(reps: Int) = repeat(reps) {
    var result = 0.0f
    inputsFloat.foreach { x => 
      result += jetFloat(x._1, x._2)
    }
    result
  }

  def timeDoubleDouble(reps: Int) = repeat(reps) {
    var result = DoubleDouble(0.0)
    inputsDDouble.foreach { x => 
      result += jetDDouble(x._1, x._2)
    }
    result
  }

  def timeQuadDouble(reps: Int) = repeat(reps) {
    var result = QuadDouble(0.0)
    inputsQDouble.foreach { x => 
      result += jetQDouble(x._1, x._2)
    }
    result
  }

  def timeFixedLong(reps: Int) = repeat(reps) {
    var result = 0l
    inputsFixedLong.foreach { x => 
      result += jetFixedLong(x._1, x._2)
    }
    result
  }

  def jetFloat(x1: Float, x2: Float): Float = {
    val t = (3*x1*x1 + 2*x2 - x1)

    x1 + ((2*x1*(t/(x1*x1 + 1))*
    (t/(x1*x1 + 1) - 3) + x1*x1*(4*(t/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(t/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  }

  def jetDouble(x1: Double, x2: Double): Double = {
    val t = (3*x1*x1 + 2*x2 - x1)

    x1 + ((2*x1*(t/(x1*x1 + 1))*
    (t/(x1*x1 + 1) - 3) + x1*x1*(4*(t/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(t/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  }

  def jetDDouble(x1: DoubleDouble, x2: DoubleDouble): DoubleDouble = {
    import DoubleDouble._
    val t = (3*x1*x1 + 2*x2 - x1)

    x1 + ((2*x1*(t/(x1*x1 + 1))*
    (t/(x1*x1 + 1) - 3) + x1*x1*(4*(t/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(t/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  }

  def jetQDouble(x1: QuadDouble, x2: QuadDouble): QuadDouble = {
    import QuadDouble._
    val t = (3*x1*x1 + 2*x2 - x1)

    x1 + ((2*x1*(t/(x1*x1 + 1))*
    (t/(x1*x1 + 1) - 3) + x1*x1*(4*(t/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(t/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  }

  def jetFixedLong(x1: Long, x2: Long) : Long = {
    val tmp1 = (1610612736 * x1) >> 30
    val tmp2 = (tmp1 * x1) >> 31
    val tmp3 = (1073741824 * x2) >> 30
    val tmp4 = ((tmp2 << 1) + tmp3) >> 1
    val tmp5 = ((tmp4 << 4) - x1) >> 4
    val t = tmp5
    val tmp6 = (1073741824 * x1) >> 30
    val tmp7 = (x1 * x1) >> 30
    val tmp8 = ((tmp7 << 4) + 1073741824) >> 4
    val tmp9 = (t << 27) / tmp8
    val tmp10 = (tmp6 * tmp9) >> 27
    val tmp11 = (x1 * x1) >> 30
    val tmp12 = ((tmp11 << 4) + 1073741824) >> 4
    val tmp13 = (t << 27) / tmp12
    val tmp14 = ((tmp13 << 4) - 1610612736) >> 4
    val tmp15 = (tmp10 * tmp14) >> 30
    val tmp16 = (x1 * x1) >> 30
    val tmp17 = (x1 * x1) >> 30
    val tmp18 = ((tmp17 << 4) + 1073741824) >> 4
    val tmp19 = (t << 27) / tmp18
    val tmp20 = (1073741824 * tmp19) >> 30
    val tmp21 = ((tmp20 << 5) - 1610612736) >> 5
    val tmp22 = (tmp16 * tmp21) >> 26
    val tmp23 = ((tmp15 << 3) + tmp22) >> 3
    val tmp24 = (x1 * x1) >> 30
    val tmp25 = ((tmp24 << 4) + 1073741824) >> 4
    val tmp26 = (tmp23 * tmp25) >> 28
    val tmp27 = (1610612736 * x1) >> 30
    val tmp28 = (tmp27 * x1) >> 31
    val tmp29 = (x1 * x1) >> 30
    val tmp30 = ((tmp29 << 4) + 1073741824) >> 4
    val tmp31 = (t << 27) / tmp30
    val tmp32 = (tmp28 * tmp31) >> 27
    val tmp33 = ((tmp26 << 4) + tmp32) >> 4
    val tmp34 = (x1 * x1) >> 30
    val tmp35 = (tmp34 * x1) >> 30
    val tmp36 = ((tmp33 << 6) + tmp35) >> 6
    val tmp37 = ((tmp36 << 10) + x1) >> 10
    val tmp38 = (1610612736 * x1) >> 30
    val tmp39 = (tmp38 * x1) >> 31
    val tmp40 = (1073741824 * x2) >> 30
    val tmp41 = ((tmp39 << 1) + tmp40) >> 1
    val tmp42 = ((tmp41 << 4) - x1) >> 4
    val tmp43 = (x1 * x1) >> 30
    val tmp44 = ((tmp43 << 4) + 1073741824) >> 4
    val tmp45 = (tmp42 << 27) / tmp44
    val tmp46 = (1610612736 * tmp45) >> 30
    val tmp47 = ((tmp37 << 6) + tmp46) >> 6
    val tmp48 = (x1 + (tmp47 << 10)) >> 10
    tmp48
  }

}


