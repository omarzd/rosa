/*
These benchmarks are inspired from the 
FEVS - Functional Equivalence Verification Suite
vsl.cis.udel.edu/fevs
*/

// This is taken from the FEVS Functional Equivalence Verification Suite

// The original benchmark used a screen to draw on, and thus had
// min/max coordinates. We omit this here. The universe is unconstraint.
object NBodySimulation {

  case class Body(mass: Double, x: Double, y: Double, vx: Double, vy: Double)

  val K = 9.81

  def init: List[Bodies] = ???

  def run = {
    var bodies = init
    for (step <- 0 until nsteps) {
      bodies = update(bodies)
    }
  }//ensuring something
}

  // One step of the simulation
  val update(bodies: List[Bodies]): List[Bodies] = {
    var newBodies: List[Bodies] = List.empty
    for (bodyX <- bodies) {
      var ax = 0.0
      var ay = 0.0

      for (bodyY <- 0 until numBodies if (bodyX != bodyY)) { // not ref. equality!
        val dx = bodyY.x - bodyX.x
        val dy = bodyY.y - bodyX.y
        val mass = bodyY.mass
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
      
      newBodies = newBodies :+ Body(
        bodyX.mass,
        bodyX.x + bodyX.vx, 
        bodyX.y + bodyX.vy, 
        bodyX.vx + ax, 
        bodyX.vy + ay)
    }
    newBodies
  }



}
