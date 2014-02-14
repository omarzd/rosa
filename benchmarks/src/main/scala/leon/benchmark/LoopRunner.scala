package leon
package benchmark

import ceres.common.{DoubleDouble, QuadDouble => QD}

object LoopRunner {

  def main(args: Array[String]) {

    val benchmarks = if (args.size > 0) args else Array("")

    benchmarks.foreach { _ match {
      case "cube" => cubeRoot(10.0, 5.4)
      case "newton" =>
        for(x <- List(0.18, 0.35, -0.53, 0.78, -0.99, 1.19, 1.25, -1.35, 1.89)) {
          newtonSine(x)
        }
        /*newtonSine(0.18)
        newtonSine(0.35)
        newtonSine(-0.53)
        newtonSine(0.78)
        newtonSine(-0.99)
        newtonSine(1.19)
        newtonSine(1.25)
        newtonSine(-1.35)
        newtonSine(1.89)*/
      case "harmonic" => harmonicEuler
      case "harmonicRK" => harmonicRK2
      case "harmonic4" => harmonicRK4
      //case "verhulst" => verhulst(0.5f, 45.0f, 11.0f)
      //case "lotka" => lotkaVolterra
      case "nbody" => nbody
      case "predatorPrey" => predatorPrey(20.0, 20.0)
      case _ => println("unknown benchmark")
    }}
    
  }

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


  def harmonicRK4 = {

    class HarmonicDouble(x0: Double, v0: Double) {
      var x = x0
      var v = v0
      val k = 2.3
      val h = 0.1
    
      def next = {
        val k1x = v
        val k1v = -k*x

        val k2x = v - k*h*x/2.0
        val k2v = -k*x - h*k*v/2.0

        val k3x = v - k*h*x/2.0 - h*h*k*v/4.0
        val k3v = -k*x - k*h*v/2.0 + k*k*h*h*x/4.0

        val k4x = v - k*h*x - k*h*h*v/2.0 + k*k*h*h*h*x/4.0
        val k4v = -k*x - k*h*v + k*k*h*h*x/2.0 + h*h*h*k*k*v/4.0

        x = x + h*(k1x + 2.0*k2x + 2*k3x + k4x)/6.0
        v = v + h*(k1v + 2.0*k2v + 2*k3v + k4v)/6.0
      }

      def next2 = {
        val k1x = v
        val k1v = -k*x

        val k2x = v + h*k1v/2.0
        val k2v = -k* (x + h*k1x/2.0) 

        val k3x = v + h*k2v/2.0 
        val k3v = -k* (x + h*k2x/2.0) 

        val k4x = v + h*k3v
        val k4v = -k* (x + h*k3x)

        x = x + h*(k1x + 2.0*k2x + 2*k3x + k4x)/6.0
        v = v + h*(k1v + 2.0*k2v + 2*k3v + k4v)/6.0 
      }
    }

    class HarmonicQD(x0: Double, v0: Double) {
      var x = QD(x0)
      var v = QD(v0)
      val k = QD(2.3)
      val h = QD(0.1)
    
      def next = {
        val k1x = v
        val k1v = -k*x

        val k2x = v - k*h*x/2.0
        val k2v = -k*x - h*k*v/2.0

        val k3x = v - k*h*x/2.0 - h*h*k*v/4.0
        val k3v = -k*x - k*h*v/2.0 + k*k*h*h*x/4.0

        val k4x = v - k*h*x - k*h*h*v/2.0 + k*k*h*h*h*x/4.0
        val k4v = -k*x - k*h*v + k*k*h*h*x/2.0 + h*h*h*k*k*v/4.0

        x = x + h*(k1x + 2.0*k2x + 2*k3x + k4x)/6.0
        v = v + h*(k1v + 2.0*k2v + 2*k3v + k4v)/6.0
      }

      def next2 = {
        val k1x = v
        val k1v = -k*x

        val k2x = v + h*k1v/2.0
        val k2v = -k* (x + h*k1x/2.0) 

        val k3x = v + h*k2v/2.0 
        val k3v = -k* (x + h*k2x/2.0) 

        val k4x = v + h*k3v
        val k4v = -k* (x + h*k3x)

        x = x + h*(k1x + 2.0*k2x + 2*k3x + k4x)/6.0
        v = v + h*(k1v + 2.0*k2v + 2*k3v + k4v)/6.0 
      } 
    }
    
    val d = new HarmonicDouble(0.2, 3.4)
    val q = new HarmonicQD(0.2, 3.4)

    for (i <- 0 until 500) {
      d.next2
      q.next2

      printErrors(i, d.x, d.v, q.x, q.v)
    } 
  }



  def nbody = {
    val solarMass = 4 * math.Pi * math.Pi
    val solarMassQ = QD(solarMass)
    val daysInAYear = 365.24
    val daysInAYearQ = QD(daysInAYear)


    var x = 4.84143144246472090e+00
    var y = -1.16032004402742839e+00
    var z = -1.03622044471123109e-01
    var vx = 1.66007664274403694e-03 * 365.24
    var vy = 7.69901118419740425e-03 * 365.24
    var vz = -6.90460016972063023e-05 * 365.24
    
    var xQ = QD(x)
    var yQ = QD(y)
    var zQ = QD(z)
    var vxQ = QD(vx)
    var vyQ = QD(vy)
    var vzQ = QD(vz)

    val dt = 0.1
    val dtQ = QD(0.1)

    def next = {
      val distance = math.sqrt(x*x + y*y + z*z)
      val mag = dt / (distance * distance * distance)

      val vxNew = vx - x * solarMass * mag
      val vyNew = vy - y * solarMass * mag
      val vzNew = vz - z * solarMass * mag

      val xNew = x + dt * vxNew
      val yNew = y + dt * vyNew
      val zNew = z + dt * vzNew
      x = xNew; y = yNew; z= zNew; vx = vxNew; vy = vyNew; vz = vzNew
    }

    def nextQ = {
      val distance = QD.sqrt(xQ*xQ + yQ*yQ + zQ*zQ)
      val mag = dtQ / (distance * distance * distance)

      val vxNew = vxQ - xQ * solarMassQ * mag
      val vyNew = vyQ - yQ * solarMassQ * mag
      val vzNew = vzQ - zQ * solarMassQ * mag

      val xNew = xQ + dtQ * vxNew
      val yNew = yQ + dtQ * vyNew
      val zNew = zQ + dtQ * vzNew
      xQ = xNew; yQ = yNew; zQ = zNew; vxQ = vxNew; vyQ = vyNew; vzQ = vzNew
    }    

    for (i <- 0 until 10000) {
      next
      nextQ
      val errX = xQ - QD(x)
      val errY = yQ - QD(y)
      val errZ = zQ - QD(z)

      print(i + ": ")
      //print(x + ", " + y + ", " + z)
      print(errX + ", " + errY + ", " + errZ)
      println(", rel: " + (errX / xQ) + ", " + (errY / yQ) + ", " + (errZ / zQ))
      
    } 
    
  }

  // Equations and initial values taken from Feedback Systems by Astrom and Murray
  def predatorPrey(x0: Double, y0: Double) = {
    var x = x0  // hares
    var y = y0  // lynxes
    var xQ = QD(x)
    var yQ = QD(y)

    val r = 1.6
    val k = 125.0
    val a = 3.2
    val b = 0.6
    val c = 50.0
    val d = 0.56

    val rQ = QD(r)
    val kQ = QD(k)
    val aQ = QD(a)
    val bQ = QD(b)
    val cQ = QD(c)
    val dQ = QD(d)
    
    val dt = 0.1
    val dtQ = QD(dt)
    val one = QD(1.0)

    def next = {
      x = x + dt * ( r*x*(1.0 - x/k) - ((a*x*y)/(c + x)) )
      y = y + dt * ( b*((a*x*y)/(c + x)) - d*y )
    }

    def nextQ = {
      xQ = xQ + dtQ * ( rQ*xQ*(one - xQ/kQ) - ((aQ*xQ*yQ)/(cQ + xQ)) )
      yQ = yQ + dtQ * ( bQ*((aQ*xQ*yQ)/(cQ + xQ)) - dQ*yQ )
    }

    
    for (i <- 0 until 500) {
      next
      nextQ

      printErrors(i, x, y, xQ, yQ)
    }
  }

  private def printErrors(i: Int, x: Double, y: Double, xQ: QD, yQ: QD) = {
    val errX = xQ - QD(x)
    val errY = yQ - QD(y)
      
    print(i + ": ")
    print(x + ", " + y + " ")
    print(errX + ", " + errY)
    println(", rel: " + (errX / xQ) + ", " + (errY / yQ))
  }



  /*def verhulst(r: Float, K: Float, x0: Float) = {
    val rQ = QD(r)
    val KQ = QD(K)
    val dt = 0.1f
    val dtQ = QD(0.1)

    def next(n: Float): Float = {
      n + dt * (r * n * (1.0f - n/K))
    }

    def nextQ(n: QD): QD = {
      n + dtQ * (rQ * n * (QD(1.0) - n/KQ)) 
    }

    var xn = x0
    var xq = QD(x0)

    println("\nverhulst, N0: " + x0 + " r:" + r + " K:" + K)
    
    for (i <- 0 until 500) {
      val xi = next(xn)
      val xiq = nextQ(xq)
      
      val errX = xiq - QD(xi)
      
      print(i + ": ")
      //println(xi + "  -  " + xiq)
      //println(xiQ + "  -  " + viQ)
      print("x: " + xi + ", " + errX )
      println(", rel: " + (errX / xq))
      xn = xi; xq = xiq
    }
  }

  def lotkaVolterra = {
    val a = 1.1
    val b = 0.31
    val c = 0.043
    val d = 0.57

    val aQ = QD(a)
    val bQ = QD(b)
    val cQ = QD(c)
    val dQ = QD(d)

    val dt = 0.05
    val dtQ = QD(dt)

    def next(n: Double, p: Double): (Double, Double) = {
      ( n + dt * (n * (a - b*p)) , p + dt * (p*(c*n - d)) )
    }

    def nextQ(n: QD, p: QD): (QD, QD) = {
      ( n + dtQ * (n * (aQ - bQ*p)) , p + dt * (p*(cQ*n - dQ)) )
    }

    var nn = 5.0
    var pn = 2.0
    var nnQ = QD(nn)
    var pnQ = QD(pn)

    for (i <- 0 until 1000) {
      val (ni, pi) = next(nn, pn)
      val (niQ, piQ) = nextQ(nnQ, pnQ)
      val errN = niQ - QD(ni)
      val errP = piQ - QD(pi)

      print(i + ": ")
      //println(xi + "  -  " + vi)
      //println(xiQ + "  -  " + viQ)
      print("N: " + ni + ", " + errN )
      print(", P: " + pi + ", " + errP)
      println(", rel: " + (errN / niQ) + ", " + (errP / piQ))
      nn = ni; pn = pi; nnQ = niQ; pnQ = piQ
    } 
  }*/
}