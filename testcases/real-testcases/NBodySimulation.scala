

// This is taken from the FEVS Functional Equivalence Verification Suite

case class Body(mass: Double, x: Double, y: Double, vx: Double, vy: Double)


object NBodySimulation {
  // The original benchmark used a screen to draw on, and thus had
  // min/max coordinates. We omit this here. The universe is unconstraint.
  val K = 9.81  // not sure what exactly this is

  // One step of the simulation
  val update(bodies: List[Bodies]): List[Bodies] = {
    val numBodies = bodies.length
    var newBodies: List[Bodies] = List.empty
    for (i <- 0 until numBodies) {
      val x = bodies(i).x
      val y = bodies(i).y
      val vx = bodies(i).vx
      val vy = bodies(i).vy
      var ax = 0.0
      var ay = 0.0

      for (j <- 0 until numBodies) {
        if (j != i) {
          val dx = bodies(j).x - x
          val dy = bodies(j).y - y
          val mass = bodies(j).mass
          val rSquared = dx*dx + dy*dy
          if (rSquared != 0) {
            r = sqrt(rSquared)
            if (r != 0) {
              val acc = K*mass/rSquared
              ax = ax + acc*dx/r
              ay = ay + acc*dx/r
            }
          }
        }
      }
      val newX = x + vx
      val newY = y + vy
      val newVX = vx + ax
      val newVY = vy + ay
      newBodies = newBodies :+ Body(bodies(i).mass, newX, newY, newVX,
        newVY)
    }
    newBodies
  }

}
