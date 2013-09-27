/*
These benchmarks are inspired from the 
FEVS - Functional Equivalence Verification Suite
vsl.cis.udel.edu/fevs
*/

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


object FEVSBenchmarks {

  // Recursive integration with the trapezoid rule.
  // In the original benchmark f was sin or cos and the interval of
  // integration [0, pi]
  def integrate(a: Double, b: Double, fa: Double, fb: Double, area: Double,
    tolerance: Double, f: Double => Double) {
    val delta = b - a
    val c = a + delta/2.0
    val fc = f(c)
    leftArea = (fa + fc) * delta/4.0
    rightArea = (fc + fb) * delta/4.0

    if (tolerance < epsilon) {
      leftArea + rightArea
    } else if (abs(leftArea + rightArea - area) <= tolerance) {
      leftArea + rightArea
    } else {
      integrate(a, c, fa, fc, leftArea, tolerance/2.0, f) +
      integrate(c, b, fc, fb, rightArea, tolerance/2.0, f)
    }
  }


  // The original reads numbers from a file,
  // we fix the number of inputs to 6.
  def meanSpec(x1: Double, x2: Double, x3: Double, x4: Double, x5: Double,
    x6: Double): Double = {
    //require(\forall \inputs \in [a, b])

    val sum = x1 + x2 + x3 + x4 + x5 + x6
    sum / 6.0
    // No overflow...
  } ensuring(res => res <= 900)

  // Keeps a running counter
  def meanImpl(x1: Double, x2: Double, x3: Double, x4: Double, x5: Double,
    x6: Double): Double = {
    //require(\forall \inputs \in [a, b])

    val i1 = x1
    val i2 = (x + x2)/2.0
    val i3 = (2*x + x3)/3.0
    val i4 = (3*x + x4)/4.0
    val i5 = (4*x + x5)/5.0
    val i6 = (5*x + x6)/6.0
    i6
  } ensuring(res => res <= 900)

  // Computes an approximation of the golden ratio using Fibonacci numbers
  def fibSpec(tol: Double) = {
    require(tol > 0.0)
    var i = 1.0
    var j = 1.0
    var err = 0.0
    var tmp = 0.0
    var p = 0.0
    err = tol

    while(err >= tol) {
      i = j
      j = k
      k = i + j
      tmp = k / j
      if (tmp >= p)
        err = tmp - p
      else
        err = p - tmp
      p = tmp
    }
    p
  } ensuring (res => res <= (1 + sqrt(5))/2.0 + tol)

  // Computes an approximation of the golden ratio using Fibonacci numbers
  def fibImpl(tol: Double) = {
    require(tol > 0.0)
    var j = 1.0
    var k = 1.0
    var err = 0.0
    var p = 0.0
    err = tol

    while(err >= tol) {
      k = j + k
      j = k - j
      err = k/j - p
      p = err + p
      if (err < 0) err = -err
    }
    p
  } ensuring (res => res <= (1 + sqrt(5))/2.0 + tol)

  // Simulated the diffusion on a domain.
  // I.e. in each time step it computes the new temperature at each
  // point in the domain
  // Let's simulate one timestep
  def diffusionSpec(initTemp: Double) {
    // Lenght of the rod is 1. The endpoints are frozen at the input temp.

    val nx = 10 // number of points in the x direction
    //val nsteps = 10 // number of time steps
    var k = 0.3 // thermal conductivity apparently
    // This is rubbish as the temp won't change this way
    val u = Array(initTemp, 100.0, 100.0, 100.0, 100.0, 100.0,
      100.0, 100.0, 100.0, initTemp)
    val uNew = Array.fill(nx)(0.0)
    for (i <- 1 until (nx - 1)) {
      uNew(i) = u(i) + k*(u(i+1) + u(i-1) - 2*u(i))
    }
    uNew
  } ensuring (res => true) //??

  // Computes the matrix product of two matrices
  // We will limit this to 3x3 matrices
  // There is also a vectorized version, si jamais
  def matmatSpec(A: Array[Array[Double]], B: Array[Array[Double]]):
    Array[Array[Double]] = {
    // require(matrices are 3 by 3)
    val C = Array[Double].fill(0.0, 0.0)

    for (i <- 0 until 3) {
      for (j <- 0 until 3) {
        C(i)(j) = 0.0
        for (k <- 0 until 3) {
          C(i)(j) = C(i)(j) + A(i)(k) * B(k)(j)
        }
      }
    }
    C
  }


}

