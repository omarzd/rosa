package leon
package experiments

import ceres.common.{DoubleDouble, QuadDouble => QD}

object IterativeExperiments {

  def cubeRoot(a: Double, x0: Double) = {
    val aq = QD(a)

    def cube(xn: Double): Double = {
      xn * ((xn*xn*xn + 2.0*a)/(2.0*xn*xn*xn + a))
    }

    def cubeQ(xn: QD): QD = {
      xn * ((xn*xn*xn + QD(2.0)*aq)/(QD(2.0)*xn*xn*xn + aq))
    }

    var x = x0
    var xq = QD(x0)
    
    for (i <- 0 until 10) {
      val xi = cube(x)
      val xiq = cubeQ(xq)
      
      val errX = xiq - QD(xi)
      
      print(i + ": ")
      //println(xi + "  -  " + xiq)
      //println(xiQ + "  -  " + viQ)
      print("x: " + xi + ", " + errX )
      println(", rel: " + (errX / xq))
      x = xi; xq = xiq
    }
  }

  def newtonSine(x0: Double) = {
    //val aq = QD(a)

    def newton(x: Double): Double = {
      x - (x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0) / 
        (1 - (x*x)/2.0 + (x*x*x*x)/24.0 + (x*x*x*x*x*x)/720.0)
    }

    def newtonQ(x: QD): QD = {
      x - (x - (x*x*x)/QD(6.0) + (x*x*x*x*x)/QD(120.0) + (x*x*x*x*x*x*x)/QD(5040.0)) / 
        (QD(1) - (x*x)/QD(2.0) + (x*x*x*x)/QD(24.0) + (x*x*x*x*x*x)/QD(720.0) )
    }

    var xn = x0
    var xq = QD(x0)

    println("\nnewton, x0: " + x0)
    
    for (i <- 0 until 20) {
      val xi = newton(xn)
      val xiq = newtonQ(xq)
      
      val errX = xiq - QD(xi)
      
      print(i + ": ")
      //println(xi + "  -  " + xiq)
      //println(xiQ + "  -  " + viQ)
      print("x: " + xi + ", " + errX )
      println(", rel: " + (errX / xq))
      xn = xi; xq = xiq
    }
  }
}