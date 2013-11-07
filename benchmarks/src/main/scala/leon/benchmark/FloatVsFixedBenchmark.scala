package leon
package benchmark

import annotation.tailrec
import com.google.caliper.Param

import scala.util.Random._

// a caliper benchmark is a class that extends com.google.caliper.Benchmark
// the SimpleScalaBenchmark trait does it and also adds some convenience functionality
class FloatVsFixedBenchmark extends SimpleScalaBenchmark {

  def floatToLong(d: Float, f: Int): Long = (d * math.pow(2, f)).round.toLong
  def longToDouble(i: Long, f: Int): Double = i.toDouble / math.pow(2, f)
  
  @Param(Array("10", "100", "1000", "10000"))
  val length: Int = 0
  
  var inputsFloatSine: Array[Float] = _
  var inputsFixedSine: Array[Long] = _
  
  var inputsFloatSineOrder3: Array[Float] = _
  var inputsFixedSineOrder3: Array[Long] = _
  
  var inputsFloatSqrt: Array[Float] = _
  var inputsFixedSqrt: Array[Long] = _
  

  override def setUp() {
    def getRandomFloatSine: Float = if (nextFloat < 0.5) - nextFloat * 1.57079632679f else nextFloat * 1.57079632679f
    def getRandomFloatSineOrder3: Float = if (nextFloat < 0.5) - nextFloat * 2.0f else nextFloat * 2.0f
    def getRandomFloatSqrt: Float = nextFloat
    
    inputsFloatSine = Array.fill(length) { getRandomFloatSine }
    inputsFixedSine = inputsFloatSine.map(i => floatToLong(i, 30))

    inputsFloatSineOrder3 = Array.fill(length) { getRandomFloatSineOrder3 }
    inputsFixedSineOrder3 = inputsFloatSineOrder3.map(i => floatToLong(i, 29))

    inputsFloatSqrt = Array.fill(length) { getRandomFloatSqrt }
    inputsFixedSqrt = inputsFloatSqrt.map(i => floatToLong(i, 30))

  }

  def timeFloatSine(reps: Int) = repeat(reps) {
    var result = 0.0f
    inputsFloatSine.foreach { x => 
      result += sine(x)
    }
    result
  }

  def timeFixedSine(reps: Int) = repeat(reps) {
    var result = 0.0f
    inputsFixedSine.foreach { x => 
      result += sineFixed(x)
    }
    result
  }

  def timeFloatSineOrder3(reps: Int) = repeat(reps) {
    var result = 0.0f
    inputsFloatSineOrder3.foreach { x => 
      result += sineOrder3(x)
    }
    result
  }

  def timeFixedSineOrder3(reps: Int) = repeat(reps) {
    var result = 0.0f
    inputsFixedSineOrder3.foreach { x => 
      result += sineOrder3Fixed(x)
    }
    result
  }

  def timeFloatSqrt(reps: Int) = repeat(reps) {
    var result = 0.0f
    inputsFloatSqrt.foreach { x => 
      result += sqroot(x)
    }
    result
  }

  def timeFixedSqrt(reps: Int) = repeat(reps) {
    var result = 0.0f
    inputsFixedSqrt.foreach { x => 
      result += sqrootFixed(x)
    }
    result
  }


  def sine(x: Float): Float = {
    //require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0f + (x*x*x*x*x)/120.0f - (x*x*x*x*x*x*x)/5040.0f 
  } //ensuring (res => res +/- 1e-6)

  def sineOrder3(x: Float): Float = {
    //require(-2.0 < x && x < 2.0)
    0.954929658551372f * x -  0.12900613773279798f*(x*x*x)
  } //ensuring (res => res +/- 1e-6)

  def sqroot(x: Float): Float = {
    //require(x >= 0.0 && x < 1.0)
    1.0f + 0.5f*x - 0.125f*x*x + 0.0625f*x*x*x - 0.0390625f*x*x*x*x
  } //ensuring (res => res +/- 1e-6)

  def sineOrder3Fixed(x : Long) : Long = {
    val tmp1 = ((2050695827 * x) >> 30)
    val tmp2 = ((x * x) >> 30)
    val tmp3 = ((tmp2 * x) >> 30)
    val tmp4 = ((1108154285 * tmp3) >> 30)
    val tmp5 = (tmp1 - tmp4)
    tmp5
  }

  def sineFixed(x : Long) : Long = {
    val tmp6 = ((x * x) >> 31)
    val tmp7 = ((tmp6 * x) >> 30)
    val tmp8 = ((tmp7 << 30) / 1610612736)
    val tmp9 = ((x << 1) - tmp8)
    val tmp10 = ((x * x) >> 31)
    val tmp11 = ((tmp10 * x) >> 30)
    val tmp12 = ((tmp11 * x) >> 31)
    val tmp13 = ((tmp12 * x) >> 31)
    val tmp14 = ((tmp13 << 28) / 2013265920)
    val tmp15 = ((tmp9 + tmp14) >> 1)
    val tmp16 = ((x * x) >> 31)
    val tmp17 = ((tmp16 * x) >> 30)
    val tmp18 = ((tmp17 * x) >> 31)
    val tmp19 = ((tmp18 * x) >> 31)
    val tmp20 = ((tmp19 * x) >> 30)
    val tmp21 = ((tmp20 * x) >> 31)
    val tmp22 = ((tmp21 << 23) / 1321205760)
    val tmp23 = ((tmp15 << 1) - tmp22)
    tmp23
  }


  def sqrootFixed(x : Long) : Long = {
    val tmp24 = ((1073741824 * x) >> 30)
    val tmp25 = (((1073741824 << 1) + tmp24) >> 1)
    val tmp26 = ((1073741824 * x) >> 32)
    val tmp27 = ((tmp26 * x) >> 30)
    val tmp28 = (((tmp25 << 1) - tmp27) >> 1)
    val tmp29 = ((1073741824 * x) >> 33)
    val tmp30 = ((tmp29 * x) >> 30)
    val tmp31 = ((tmp30 * x) >> 30)
    val tmp32 = (((tmp28 << 1) + tmp31) >> 1)
    val tmp33 = ((1342177280 * x) >> 34)
    val tmp34 = ((tmp33 * x) >> 30)
    val tmp35 = ((tmp34 * x) >> 30)
    val tmp36 = ((tmp35 * x) >> 30)
    val tmp37 = (((tmp32 << 1) - tmp36) >> 1)
    tmp37
  }

}