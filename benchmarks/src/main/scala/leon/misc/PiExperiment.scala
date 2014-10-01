package leon
package misc

import ceres.common.{DoubleDouble, QuadDouble => QD}

object PiExperiment {

  def main(args: Array[String]) {
    piFloat

    println("-----------\n")

    piMixed
  }

  def piFloat = {
    val pi4 = math.Pi

    val pi4_1 = pi_4(2)
    println(2 + "  -  " + (pi4 - pi4_1))

    val pi4_2 = pi_4(20)
    println(20 + "  -  " + (pi4 - pi4_2))

    val pi4_3 = pi_4(200)
    println(200 + "  -  " + (pi4 - pi4_3))

    val pi4_4 = pi_4(2000)
    println(2000 + "  -  " + (pi4 - pi4_4))

    val pi4_5 = pi_4(20000)
    println(20000 + "  -  " + (pi4 - pi4_5))

    val pi4_6 = pi_4(200000)
    println(200000 + "  -  " + (pi4 - pi4_6))

    val pi4_7 = pi_4(2000000)
    println(2000000 + "  -  " + (pi4 - pi4_7))

    val pi4_8 = pi_4(20000000)
    println(20000000 + "  -  " + (pi4 - pi4_8))

    val pi4_9 = pi_4(200000000)
    println(200000000 + "  -  " + (pi4 - pi4_9))
  }

  def piMixed = {
    //val pi4 = math.Pi
    val pi4 = 3.141592653589793238462643383279502884197

    val pi4_1 = pi_mixed(2)
    println(2 + "  -  " + (pi4 - pi4_1))

    val pi4_2 = pi_mixed(20)
    println(20 + "  -  " + (pi4 - pi4_2))

    val pi4_3 = pi_mixed(200)
    println(200 + "  -  " + (pi4 - pi4_3))

    val pi4_4 = pi_mixed(2000)
    println(2000 + "  -  " + (pi4 - pi4_4))

    val pi4_5 = pi_mixed(20000)
    println(20000 + "  -  " + (pi4 - pi4_5))

    val pi4_6 = pi_mixed(200000)
    println(200000 + "  -  " + (pi4 - pi4_6))

    val pi4_7 = pi_mixed(2000000)
    println(2000000 + "  -  " + (pi4 - pi4_7))

    val pi4_8 = pi_mixed(20000000)
    println(20000000 + "  -  " + (pi4 - pi4_8))

    val pi4_9 = pi_mixed(200000000)
    println(200000000 + "  -  " + (pi4 - pi4_9))
  }

  def pi_mixed (n: Int): Float = {
    var i = 0
    var sum = 0.0f
    val dx: Float = (1.0/n).toFloat

    for(i <- 0 until n){
      val x: Float = dx/2.0f + dx*i
      val mypart: Float = 1.0f/(1.0f + x*x)
      sum += mypart
    }
    4.0f*sum*dx
  }

  def pi_4 (n: Int): Float = {
    var i = 0
    var sum = 0.0f
    val dx = 1.0f/n

    for(i <- 0 until n){
      val x: Float = dx/2.0f + dx*i
      val mypart: Float = 1.0f/(1.0f + x*x)
      sum += mypart
    }
    4.0f*sum*dx
  }

  /*def pi_4 (n: Int): Double = {
    var i = 0
    var sum = 0.0
    val dx = 1.0/n

    for(i <- 0 until n){
      val x = dx/2.0 + dx*i
      val mypart = 1.0/(1.0 + x*x)
      sum += mypart
    }
    sum*dx
  }*/

}