package leon
package benchmark

import ceres.common.{DoubleDouble, QuadDouble => QD}

object LoopRunner {

  def main(args: Array[String]) {

    val benchmarks = if (args.size > 0) args else Array("")

    benchmarks.foreach { _ match {
      case "cube" => cubeRootUnrolled(10.0, 3.4) 
      case "harmonic" => harmonicEuler
      case "harmonicRK" => harmonicRK2
      case _ => println("unknown benchmark")
    }}
    
  }

  def cubeRootUnrolled(a: Double, x0: Double) = {
    val xn = x0
    val xnq = QD(xn)

    // iteration 1
    val xn1 = xn * ((xn*xn*xn + 2.0*a)/(2.0*xn*xn*xn + a))
    val xn1q = xnq * ((xnq*xnq*xnq + 2.0*a)/(2.0*xnq*xnq*xnq + a))
    val e1 = xn1q - QD(xn1)
    println("1: " + xn1 + "  -  " + xn1q)
    println(e1)

    // iteration 2
    val xn2 = xn1 * ((xn1*xn1*xn1 + 2.0*a)/(2.0*xn1*xn1*xn1 + a))
    val xn2q = xn1q * ((xn1q*xn1q*xn1q + 2.0*a)/(2.0*xn1q*xn1q*xn1q + a))
    val e2 = xn2q - QD(xn2)
    println("\n2: " + xn2 + "  -  " + xn2q)
    println(e2)
    
    // iteration 3
    val xn3 = xn2 * ((xn2*xn2*xn2 + 2.0*a)/(2.0*xn2*xn2*xn2 + a))
    val xn3q = xn2q * ((xn2q*xn2q*xn2q + 2.0*a)/(2.0*xn2q*xn2q*xn2q + a))
    val e3 = xn3q - QD(xn3)
    println("\n3: " + xn3 + "  -  " + xn3q)
    println(e3)
    
    // iteration 4
    val xn4 = xn3 * ((xn3*xn3*xn3 + 2.0*a)/(2.0*xn3*xn3*xn3 + a))
    val xn4q = xn3q * ((xn3q*xn3q*xn3q + 2.0*a)/(2.0*xn3q*xn3q*xn3q + a))
    val e4 = xn4q - QD(xn4)
    println("\n4: " + xn4 + "  -  " + xn4q)
    println(e4)
    

    // iteration 5
    val xn5 = xn4 * ((xn4*xn4*xn4 + 2.0*a)/(2.0*xn4*xn4*xn4 + a))
    val xn5q = xn4q * ((xn4q*xn4q*xn4q + 2.0*a)/(2.0*xn4q*xn4q*xn4q + a))
    val e5 = xn5q - QD(xn5)
    println("\n5: " + xn5 + "  -  " + xn5q)
    println(e5)
  }

  def harmonicEuler = {
    val k = 2.3
    val dt = 0.1
    val kQ = QD(2.3)
    val dtQ = QD(0.1)

    def next(x: Double, v: Double): (Double, Double) = {
      (x + v*dt, v + (-k*x*dt))
    }

    def nextQ(x: QD, v: QD): (QD, QD) = {
      (x + v*dtQ, v + (-kQ*x*dtQ))
    }

    var xn = 0.2
    var vn = 3.4
    var xnQ = QD(xn)
    var vnQ = QD(vn)

    for (i <- 0 until 300) {
      val (xi, vi) = next(xn, vn)
      val (xiQ, viQ) = nextQ(xnQ, vnQ)
      val errX = xiQ - QD(xi)
      val errV = viQ - QD(vi)

      print(i + ": ")
      //println(xi + "  -  " + vi)
      //println(xiQ + "  -  " + viQ)
      print("x: " + xi + ", " + errX )
      println(", rel: " + (errX / xiQ))
      xn = xi; vn = vi; xnQ = xiQ; vnQ = viQ
    } 
  }

  def harmonicRK2 = {
    val k = 2.3
    val dt = 0.1
    val kQ = QD(2.3)
    val dtQ = QD(0.1)

    def next(x: Double, v: Double): (Double, Double) = {
      val dx = dt * (v + (-k*x*dt/2))
      val dv = dt * (-k)* (x + v*dt/2)
      (x + dx, v + dv)
    }

    def nextQ(x: QD, v: QD): (QD, QD) = {
      val dx = dtQ * (v + (-kQ*x*dtQ/2))
      val dv = dtQ * (-kQ)* (x + v*dtQ/2)
      (x + dx, v + dv)
    }

    var xn = 0.2
    var vn = 3.4
    var xnQ = QD(xn)
    var vnQ = QD(vn)

    for (i <- 0 until 300) {
      val (xi, vi) = next(xn, vn)
      val (xiQ, viQ) = nextQ(xnQ, vnQ)
      val errX = xiQ - QD(xi)
      val errV = viQ - QD(vi)

      print(i + ": ")
      //println(xi + "  -  " + vi)
      //println(xiQ + "  -  " + viQ)
      print("x: " + xi + ", " + errX )
      println(", rel: " + (errX / xiQ))
      xn = xi; vn = vi; xnQ = xiQ; vnQ = viQ
    } 
  }
  
}