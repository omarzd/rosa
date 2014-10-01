package leon
package benchmark

import annotation.tailrec
import com.google.caliper.Param

import scala.util.Random._

import ceres.common.{DoubleDouble, QuadDouble}

// a caliper benchmark is a class that extends com.google.caliper.Benchmark
// the SimpleScalaBenchmark trait does it and also adds some convenience functionality
class SineBenchmark extends SimpleScalaBenchmark with Utils {

  @Param(Array("10", "100", "1000", "10000"))
  val length: Int = 0
  
  var inputsFloat: Array[Float] = _
  var inputsDouble: Array[Double] = _
  var inputsDDouble: Array[DoubleDouble] = _
  var inputsQDouble: Array[QuadDouble] = _
  
  var inputsFixedInt: Array[Int] = _ //16 bit is not possible
  var inputsFixedLong: Array[Long] = _

  override def setUp() {
    def getX: Float = nextFloat * 2f
      
    inputsFloat = Array.fill(length) { getX }
    inputsDouble = inputsFloat.map(i => i.toDouble)
    inputsDDouble = inputsDouble.map(i => DoubleDouble(i))
    inputsQDouble = inputsFloat.map(i => QuadDouble(i))

    inputsFixedInt = inputsFloat.map(i => floatToInt(i, 13))
    inputsFixedLong = inputsFloat.map(i => floatToLong(i, 29))
  }
  
  def timeFloat(reps: Int) = repeat(reps) {
    var result = 0.0f
    inputsFloat.foreach { x => 
      result += sineFloat(x)
    }
    result
  }

  def timeDouble(reps: Int) = repeat(reps) {
    var result = 0.0
    inputsFloat.foreach { x => 
      result += sineDouble(x)
    }
    result
  }

  def timeDoubleDouble(reps: Int) = repeat(reps) {
    var result = DoubleDouble(0.0)
    inputsDDouble.foreach { x => 
      result += sineDoubleDouble(x)
    }
    result
  }

  def timeQuadDouble(reps: Int) = repeat(reps) {
    var result = QuadDouble(0.0)
    inputsQDouble.foreach { x => 
      result += sineQuadDouble(x)
    }
    result
  }

  def timeFixedInt(reps: Int) = repeat(reps) {
    var result = 0
    inputsFixedInt.foreach { x => 
      result += sineFixedInt(x)
    }
    result
  }

  def timeFixedLong(reps: Int) = repeat(reps) {
    var result = 0l
    inputsFixedLong.foreach { x => 
      result += sineFixedLong(x)
    }
    result
  }

  def sineFloat(x: Float): Float = {
    x - (x*x*x)/6.0f + (x*x*x*x*x)/120.0f - (x*x*x*x*x*x*x)/5040.0f 
  }

  def sineDouble(x: Double): Double = {
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 - (x*x*x*x*x*x*x)/5040.0 
  } 
  
  def sineDoubleDouble(x: DoubleDouble): DoubleDouble = {
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 - (x*x*x*x*x*x*x)/5040.0 
  }

  def sineQuadDouble(x: QuadDouble): QuadDouble = {
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 - (x*x*x*x*x*x*x)/5040.0 
  }

  //u -> <1,32,24>v -> <1,32,16>#T -> <1,32,25>
  def sineFixedInt(x: Int) : Int = {
    val _tmp1 = ((x * x) >> 14)
    val _tmp2 = ((_tmp1 * x) >> 14)
    val _tmp3 = ((_tmp2 << 15) / 24576)
    val _tmp4 = (((x << 1) - _tmp3) << 1)
    val _tmp5 = ((x * x) >> 14)
    val _tmp6 = ((_tmp5 * x) >> 14)
    val _tmp7 = ((_tmp6 * x) >> 14)
    val _tmp8 = ((_tmp7 * x) >> 14)
    val _tmp9 = ((_tmp8 << 14) / 30720)
    val _tmp10 = ((_tmp4 + _tmp9) >> 1)
    val _tmp11 = ((x * x) >> 14)
    val _tmp12 = ((_tmp11 * x) >> 14)
    val _tmp13 = ((_tmp12 * x) >> 14)
    val _tmp14 = ((_tmp13 * x) >> 14)
    val _tmp15 = ((_tmp14 * x) >> 14)
    val _tmp16 = ((_tmp15 * x) >> 14)
    val _tmp17 = ((_tmp16 << 10) / 20160)
    val _tmp18 = (((_tmp10 << 1) - _tmp17) >> 1)
    _tmp18
  }

  def sineFixedLong(x: Long): Long = {
    val _tmp1 = ((x * x) >> 30)
    val _tmp2 = ((_tmp1 * x) >> 30)
    val _tmp3 = ((_tmp2 << 31) / 1610612736l)
    val _tmp4 = (((x << 1) - _tmp3) << 1)
    val _tmp5 = ((x * x) >> 30)
    val _tmp6 = ((_tmp5 * x) >> 30)
    val _tmp7 = ((_tmp6 * x) >> 30)
    val _tmp8 = ((_tmp7 * x) >> 30)
    val _tmp9 = ((_tmp8 << 30) / 2013265920l)
    val _tmp10 = ((_tmp4 + _tmp9) >> 1)
    val _tmp11 = ((x * x) >> 30)
    val _tmp12 = ((_tmp11 * x) >> 30)
    val _tmp13 = ((_tmp12 * x) >> 30)
    val _tmp14 = ((_tmp13 * x) >> 30)
    val _tmp15 = ((_tmp14 * x) >> 30)
    val _tmp16 = ((_tmp15 * x) >> 30)
    val _tmp17 = ((_tmp16 << 26) / 1321205760l)
    val _tmp18 = ((_tmp10 << 1) - _tmp17)
    _tmp18
  }
}