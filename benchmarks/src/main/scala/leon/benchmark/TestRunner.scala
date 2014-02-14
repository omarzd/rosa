package leon
package benchmark


object TestRunner {

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
      
      case _ => println("unknown benchmark")
    }}
    
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


  
}