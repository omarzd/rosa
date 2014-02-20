package leon
package benchmark

import java.io.{PrintWriter, File}

object TestRunner {
  var writer: PrintWriter = null


  def main(args: Array[String]) {

    val benchmarks = if (args.size > 0) args else Array("oneBody")

        
    benchmarks.foreach { _ match {
      case "oneBody" =>
        // apparently jupiter:
        val px = 4.84143144246472090
        val py = -1.16032004402742839
        val vx = 1.66007664274403694e-03 * 365.25
        val vy = 7.69901118419740425e-03 * 365.25 

        oneBody(3.5, 0.0, 0.0, 1.4, 0.0) 
      
      case "spiral" =>
        writer = new PrintWriter(new File("spiral.txt"))
        println("Spiral:")
        spiral(7.0, 7.0, 1000)
        writer.close()

      case "nBody" =>
        writer = new PrintWriter(new File("nbody.txt"))
        simulate(1000)
        writer.close()



      case _ => println("unknown benchmark")
    }}
    
  }


  def spiral(x: Double, y: Double, k: Int): (Double, Double) = {
    require(x*x + y*y < 100 && -10 <= x && x <= 10 && -10 <= y && y <= 10)
    
    println(x + " " + y)
    writer.write(x + " " + y + "\n")
        
    if (k > 0) {
      val x1 = (9.9*x - y)/10
      val y1 = (9.9*y + x)/10
      spiral(x1,y1,k-1)
    } else {
      (x, y)
    }
  }

  def oneBody(x: Double, y: Double, u: Double, v: Double, t: Double): (Double, Double) = {
    val M: Double = 1.0
    val m: Double = 0.12 
    val G: Double = 6.67
    val dt = 0.1

    println("" + x + ", " + y + " -- " + u + ", " + v)

    if(t < 100.0) {
      val dx = -x
      val dy = -y
      val r2 = dx*dx + dy*dy
      val r = math.sqrt(r2)

      val F = G * M / r2
      val ax = F * dx / r
      val ay = F * dy / r

      //println("\na: " + ax + ", " + ay)
      val newU = u + ax * dt
      val newV = v + ay * dt

      //println("v: " + newU + ", " + newV)
      

      val newX = x + newU * dt
      val newY = y + newV * dt

      //println("x: " + newX + ", " + newY)

      
      oneBody(newX, newY, newU, newV, t + dt)
    } else {
      (x, y)
    }

  }

  /*
      NBODY simulation of the solar system from the Benchmark game
  */
  def simulate(N: Int): Long = {
    var n = N
    printf("%.9f\n", JovianSystem.energy )
    val start = System.currentTimeMillis
    while (n > 0) { 
      JovianSystem.advance(0.01)
      println(JovianSystem)
      writer.write(JovianSystem.toString + "\n")
      n -= 1 
    }
    val end = System.currentTimeMillis
    printf("%.9f\n", JovianSystem.energy )
    //println("time taken " + (end - start) + " ms")
    return (end - start)
  }

}

abstract class NBodySystem {

  def energy() = {
    var e = 0.0
    
    for (i <- 0 until bodies.length) {
      e += 0.5 * bodies(i).mass * bodies(i).speedSq
      
      for (j <- i+1 until bodies.length) {
        val dx = bodies(i).x - bodies(j).x
        val dy = bodies(i).y - bodies(j).y
        val dz = bodies(i).z - bodies(j).z
        val distance = math.sqrt(dx*dx + dy*dy + dz*dz)
        e -= (bodies(i).mass * bodies(j).mass) / distance
      }
    }
    e
  }

  def advance(dt: Double) = {
    var i = 0
    while (i < bodies.length){
      var j = i+1
      while (j < bodies.length){
        val dx = bodies(i).x - bodies(j).x
        val dy = bodies(i).y - bodies(j).y
        val dz = bodies(i).z - bodies(j).z

        val distance = math.sqrt(dx*dx + dy*dy + dz*dz)
        val mag = dt / (distance * distance * distance)

        bodies(i).advance(dx,dy,dz,-bodies(j).mass*mag)
        bodies(j).advance(dx,dy,dz,bodies(i).mass*mag)

        j += 1
      }
      i += 1
    }

    i = 0
    while (i < bodies.length){
      bodies(i).move(dt)
      i += 1
    }
  }

  protected val bodies: Array[Body]

  class Body(){
    var x,y,z = 0.0
    var vx,vy,vz = 0.0
    var mass = 0.0
    def speedSq = vx*vx + vy*vy + vz*vz
    def move(dt: Double) {
      x += dt*vx
      y += dt*vy
      z += dt*vz
    }
    def advance(dx: Double, dy: Double, dz: Double, delta: Double) {
      vx += dx*delta
      vy += dy*delta
      vz += dz*delta
    }

    override def toString: String = {
      "("+x+","+y+")" //"("+x+","+y+","+z+")"
    }
  }

  override def toString: String = {
    bodies.mkString(": ")
  }
}

object JovianSystem extends NBodySystem {
   protected val bodies = initialValues

   private def initialValues() = {
      val SOLAR_MASS = 4 * math.Pi * math.Pi
      val DAYS_PER_YEAR = 365.24

      val sun = new Body
      sun.mass = SOLAR_MASS

      val jupiter = new Body
      jupiter.x = 4.84143144246472090e+00
      jupiter.y = -1.16032004402742839e+00
      jupiter.z = -1.03622044471123109e-01
      jupiter.vx = 1.66007664274403694e-03 * DAYS_PER_YEAR
      jupiter.vy = 7.69901118419740425e-03 * DAYS_PER_YEAR
      jupiter.vz = -6.90460016972063023e-05 * DAYS_PER_YEAR
      jupiter.mass = 9.54791938424326609e-04 * SOLAR_MASS

      val saturn = new Body
      saturn.x = 8.34336671824457987e+00
      saturn.y = 4.12479856412430479e+00
      saturn.z = -4.03523417114321381e-01
      saturn.vx = -2.76742510726862411e-03 * DAYS_PER_YEAR
      saturn.vy = 4.99852801234917238e-03 * DAYS_PER_YEAR
      saturn.vz = 2.30417297573763929e-05 * DAYS_PER_YEAR
      saturn.mass = 2.85885980666130812e-04 * SOLAR_MASS

      val uranus = new Body
      uranus.x = 1.28943695621391310e+01
      uranus.y = -1.51111514016986312e+01
      uranus.z = -2.23307578892655734e-01
      uranus.vx = 2.96460137564761618e-03 * DAYS_PER_YEAR
      uranus.vy = 2.37847173959480950e-03 * DAYS_PER_YEAR
      uranus.vz = -2.96589568540237556e-05 * DAYS_PER_YEAR
      uranus.mass = 4.36624404335156298e-05 * SOLAR_MASS

      val neptune = new Body
      neptune.x = 1.53796971148509165e+01
      neptune.y = -2.59193146099879641e+01
      neptune.z = 1.79258772950371181e-01
      neptune.vx = 2.68067772490389322e-03 * DAYS_PER_YEAR
      neptune.vy = 1.62824170038242295e-03 * DAYS_PER_YEAR
      neptune.vz = -9.51592254519715870e-05 * DAYS_PER_YEAR
      neptune.mass = 5.15138902046611451e-05  * SOLAR_MASS


      //val initialValues = Array ( sun, jupiter, saturn, uranus, neptune )
      val initialValues = Array ( sun, jupiter)//, saturn)//, uranus, neptune )

      var px = 0.0; var py = 0.0; var pz = 0.0;
      for (b <- initialValues){
         px += (b.vx * b.mass)
         py += (b.vy * b.mass)
         pz += (b.vz * b.mass)
      }
      sun.vx = -px / SOLAR_MASS
      sun.vy = -py / SOLAR_MASS
      sun.vz = -pz / SOLAR_MASS

      initialValues
   }
}