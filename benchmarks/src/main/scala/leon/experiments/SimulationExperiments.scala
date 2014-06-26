package leon
package experiments

import ceres.common.{DoubleDouble, QuadDouble => QD}

object SimulationExperiments {

  def harmonicEuler = {
    val k = 2.3
    val dt = 0.01
    val kQ = QD(2.3)
    val dtQ = QD(0.01)

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

    for (i <- 0 until 500) {
      val (xi, vi) = next(xn, vn)
      val (xiQ, viQ) = nextQ(xnQ, vnQ)
      val errX = xiQ - QD(xi)
      val errV = viQ - QD(vi)

      print(i + ": ")
      //println(xi + "  -  " + vi)
      //println(xiQ + "  -  " + viQ)
      print("x: " + xi + ", " + errX + " v: " + vi)
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

    for (i <- 0 until 1000) {
      next
      nextQ
      val errX = xQ - QD(x)
      val errY = yQ - QD(y)
      val errZ = zQ - QD(z)

      print(i + ": ")
      println(x + ", " + y + ", " + z + ", " + vx + ", " + vy + ", " + vz)
      
      //print(errX + ", " + errY + ", " + errZ)
      //println(", rel: " + (errX / xQ) + ", " + (errY / yQ) + ", " + (errZ / zQ))
      
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

  def predatorPreyRK2(x0: Double, y0: Double) = {
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
    
    val h = 0.1
    val hQ = QD(h)
    val one = QD(1.0)

    //f1 = r*x*(1.0 - x/k) - ((a*x*y)/(c + x))
    //f2 = b*((a*x*y)/(c + x)) - d*y

    def next = {
      val k1x = r*x*(1.0 - x/k) - ((a*x*y)/(c + x))
      val k1y = b*((a*x*y)/(c + x)) - d*y

      val k2x = r*(x + h*k1x)*(1.0 - (x + h*k1x)/k) - ((a*(x + h*k1x)*(y + h*k1y))/(c + (x + h*k1x)))
      val k2y = b*((a*(x + h*k1x)*(y + h*k1y))/(c + (x + h*k1x))) - d*(y + h*k1y)

      x = x + (h/2.0)*(k1x + k2x)
      y = y + (h/2.0)*(k1y + k2y)
    }

    def nextQ = {
      val k1x = rQ*xQ*(one - xQ/kQ) - ((aQ*xQ*yQ)/(cQ + xQ))
      val k1y = bQ*((aQ*xQ*yQ)/(cQ + xQ)) - dQ*yQ

      val k2x = rQ*(xQ + hQ*k1x)*(one - (xQ + hQ*k1x)/kQ) - ((aQ*(xQ + hQ*k1x)*(yQ + hQ*k1y))/(cQ + (xQ + hQ*k1x)))
      val k2y = bQ*((aQ*(xQ + hQ*k1x)*(yQ + hQ*k1y))/(cQ + (xQ + hQ*k1x))) - dQ*(yQ + hQ*k1y)

      xQ = xQ + (hQ/QD(2.0))*(k1x + k2x)
      yQ = yQ + (hQ/QD(2.0))*(k1y + k2y)
    }
    
    for (i <- 0 until 500) {
      next
      nextQ

      printErrors(i, x, y, xQ, yQ)
    }
  }

  def predatorPreyRK4(x0: Double, y0: Double) = {

    class PPDouble {
      var x = x0  // hares
      var y = y0  // lynxes
      
      val r = 1.6
      val k = 125.0
      val a = 3.2
      val b = 0.6
      val c = 50.0
      val d = 0.56

      val h = 0.1
      val h_2 = 0.05

      def next = {
        val k1x = r*x*(1.0 - x/k) - ((a*x*y)/(c + x))
        val k1y = b*((a*x*y)/(c + x)) - d*y

        val k2x = r*(x + h_2*k1x)*(1.0 - (x + h_2*k1x)/k) - ((a*(x + h_2*k1x)*(y + h_2*k1y))/(c + (x + h_2*k1x)))
        val k2y = b*((a*(x + h_2*k1x)*(y + h_2*k1y))/(c + (x + h_2*k1x))) - d*(y + h_2*k1y)

        val k3x = r*(x + h_2*k2x)*(1.0 - (x + h_2*k2x)/k) - ((a*(x + h_2*k2x)*(y + h_2*k2y))/(c + (x + h_2*k2x)))
        val k3y = b*((a*(x + h_2*k2x)*(y + h_2*k2y))/(c + (x + h_2*k2x))) - d*(y + h_2*k2y)

        val k4x = r*(x + h*k3x)*(1.0 - (x + h*k3x)/k) - ((a*(x + h*k3x)*(y + h*k3y))/(c + (x + h*k3x)))
        val k4y = b*((a*(x + h*k3x)*(y + h*k3y))/(c + (x + h*k3x))) - d*(y + h*k3y)

        x = x + (h/6.0)*(k1x + 2.0*k2x + 2.0*k3x + k4x)
        y = y + (h/6.0)*(k1y + 2.0*k2y + 2.0*k3y + k4y)
      }
    }
    
    class PPQD {
      var x = QD(x0)
      var y = QD(y0)

      val one = QD(1.0)

      val r = QD(1.6)
      val k = QD(125.0)
      val a = QD(3.2)
      val b = QD(0.6)
      val c = QD(50.0)
      val d = QD(0.56)

      val h = QD(0.1)
      val h_2 = 0.05

      def next = {
        val k1x = r*x*(1.0 - x/k) - ((a*x*y)/(c + x))
        val k1y = b*((a*x*y)/(c + x)) - d*y

        val k2x = r*(x + h_2*k1x)*(1.0 - (x + h_2*k1x)/k) - ((a*(x + h_2*k1x)*(y + h_2*k1y))/(c + (x + h_2*k1x)))
        val k2y = b*((a*(x + h_2*k1x)*(y + h_2*k1y))/(c + (x + h_2*k1x))) - d*(y + h_2*k1y)

        val k3x = r*(x + h_2*k2x)*(1.0 - (x + h_2*k2x)/k) - ((a*(x + h_2*k2x)*(y + h_2*k2y))/(c + (x + h_2*k2x)))
        val k3y = b*((a*(x + h_2*k2x)*(y + h_2*k2y))/(c + (x + h_2*k2x))) - d*(y + h_2*k2y)

        val k4x = r*(x + h*k3x)*(1.0 - (x + h*k3x)/k) - ((a*(x + h*k3x)*(y + h*k3y))/(c + (x + h*k3x)))
        val k4y = b*((a*(x + h*k3x)*(y + h*k3y))/(c + (x + h*k3x))) - d*(y + h*k3y)

        x = x + (h/6.0)*(k1x + 2.0*k2x + 2.0*k3x + k4x)
        y = y + (h/6.0)*(k1y + 2.0*k2y + 2.0*k3y + k4y)
      }
    }

    val d = new PPDouble
    val q = new PPQD

    for (i <- 0 until 500) {
      d.next
      q.next

      printErrors(i, d.x, d.y, q.x, q.y)
    }
  }




  private def printErrors(i: Int, x: Double, xQ: QD) = {
    val errX = xQ - QD(x)
      
    print(i + ": ")
    print(x + ", " + errX)
    println(", rel: " + (errX / xQ))
  }

  private def printErrors(i: Int, x: Double, y: Double, xQ: QD, yQ: QD) = {
    val errX = xQ - QD(x)
    val errY = yQ - QD(y)
      
    print(i + ": ")
    print(x + ", " + y + ", ")
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