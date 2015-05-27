package leon
package misc

import ceres.common.{DoubleDouble, QuadDouble => QD}
import java.io.{PrintWriter, File}

object JetEngineForTalk extends App {
  var r = new scala.util.Random(4731)
  val out = new PrintWriter(new File("jetEngine.res"))
  
  def floatToLong(d: Double, f: Int): Long = (d * math.pow(2, f)).round.toLong
  def floatToInt(d: Float, f: Int): Int = (d * math.pow(2, f)).round.toInt
  def longToDouble(i: Long, f: Int): Double = i.toDouble / math.pow(2, f)

  val x = 4.709957
  val y = -11.208681
  

  /*var i = 0
  while(i < 1000) {
    val x = -5.0f + r.nextFloat * 10.0f
    val y = -20.0f + r.nextFloat * 25.0f
  */
    val dbl = jetEngine(x, y)
    val fl = jetEngineFloat(x.toFloat, y.toFloat)
    val qd = jetEngineQD(QD(x), QD(y))

    val diff: QD = qd - dbl
    val diffFl: QD = qd - fl
  
    val fix = jetEngineFP(floatToLong(x, 28), floatToLong(y, 26))
    val diffFP: QD = qd - longToDouble(fix, 18)
    
    println(diffFl)
    println(diffFP)
    println(diff)
    println()
    println(qd)
    println(dbl)
    println(fl)
    println(longToDouble(fix, 18))
  


  /*
    if (diff > 1e-4)
      out.write(x + " " + y + " " +  diff + "\n")
    i = i + 1
  }*/

  out.close

  def jetEngine(x1: Double, x2: Double): Double = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5)

    val t = (3*x1*x1 + 2*x2 - x1)

    x1 + ((2*x1*(t/(x1*x1 + 1))*
    (t/(x1*x1 + 1) - 3) + x1*x1*(4*(t/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(t/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  }

  def jetEngineFloat(x1: Float, x2: Float): Float = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5)

    val t = (3*x1*x1 + 2*x2 - x1)

    x1 + ((2*x1*(t/(x1*x1 + 1))*
    (t/(x1*x1 + 1) - 3) + x1*x1*(4*(t/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(t/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  }


  def jetEngineQD(x1: QD, x2: QD): QD = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5)

    val t = (3*x1*x1 + 2*x2 - x1)

    x1 + ((2*x1*(t/(x1*x1 + 1))*
    (t/(x1*x1 + 1) - 3) + x1*x1*(4*(t/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(t/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  }

  def jetEngineFP(x1: Long, x2: Long) : Long = {
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
    tmp48 //#_tmp48 -> <1,32,18>
  }
}