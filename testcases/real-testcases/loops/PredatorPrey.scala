import leon.Real
import Real._

object PredatorPrey {

  def euler(x: Real, y: Real): (Real, Real) = {
    // only holds for about 5 generations
    require(0 <= x && x <= 90 && 0 <= y && y <= 70)

    iterate {
      val r: Real = 1.6
      val k: Real = 125.0
      val a: Real = 3.2
      val b: Real = 0.6
      val c: Real = 50.0
      val d: Real = 0.56

      x <== x + dt * ( r*x*(1.0 - x/k) - ((a*x*y)/(c + x)) )
      y <== y + dt * ( b*((a*x*y)/(c + x)) - d*y )
    }
  }


  def rungeKutta2(x: Real, y: Real): (Real, Real) = {
    // only holds for about 5 generations
    require(0 <= x && x <= 90 && 0 <= y && y <= 70)

    iterate {
      val r: Real = 1.6
      val k: Real = 125.0
      val a: Real = 3.2
      val b: Real = 0.6
      val c: Real = 50.0
      val d: Real = 0.56

      val k1x = r*x*(1.0 - x/k) - ((a*x*y)/(c + x))
      val k1y = b*((a*x*y)/(c + x)) - d*y

      val k2x = r*(x + h*k1x)*(1.0 - (x + h*k1x)/k) - ((a*(x + h*k1x)*(y + h*k1y))/(c + (x + h*k1x)))
      val k2y = b*((a*(x + h*k1x)*(y + h*k1y))/(c + (x + h*k1x))) - d*(y + h*k1y)

      x <== x + (h/2.0)*(k1x + k2x)
      y <== y + (h/2.0)*(k1y + k2y)
    }
  }

  def rungeKutta4(x: Real, y: Real): (Real, Real) = {
    // only holds for about 5 generations
    require(0 <= x && x <= 90 && 0 <= y && y <= 70)

    iterate {
      val r: Real = 1.6
      val k: Real = 125.0
      val a: Real = 3.2
      val b: Real = 0.6
      val c: Real = 50.0
      val d: Real = 0.56

      val k1x = r*x*(1.0 - x/k) - ((a*x*y)/(c + x))
      val k1y = b*((a*x*y)/(c + x)) - d*y

      val k2x = r*(x + h_2*k1x)*(1.0 - (x + h_2*k1x)/k) - ((a*(x + h_2*k1x)*(y + h_2*k1y))/(c + (x + h_2*k1x)))
      val k2y = b*((a*(x + h_2*k1x)*(y + h_2*k1y))/(c + (x + h_2*k1x))) - d*(y + h_2*k1y)

      val k3x = r*(x + h_2*k2x)*(1.0 - (x + h_2*k2x)/k) - ((a*(x + h_2*k2x)*(y + h_2*k2y))/(c + (x + h_2*k2x)))
      val k3y = b*((a*(x + h_2*k2x)*(y + h_2*k2y))/(c + (x + h_2*k2x))) - d*(y + h_2*k2y)

      val k4x = r*(x + h*k3x)*(1.0 - (x + h*k3x)/k) - ((a*(x + h*k3x)*(y + h*k3y))/(c + (x + h*k3x)))
      val k4y = b*((a*(x + h*k3x)*(y + h*k3y))/(c + (x + h*k3x))) - d*(y + h*k3y)

      x <== x + (h/6.0)*(k1x + 2.0*k2x + 2.0*k3x + k4x)
      y <== y + (h/6.0)*(k1y + 2.0*k2y + 2.0*k3y + k4y)
    }
  }
}