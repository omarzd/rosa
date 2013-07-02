
import leon.Real
import Real._


/**
  These benchmarks come from the fixed-point arithmetic domain.
 */
object Fixedpoint {

  def rigidBody1(x1: Real, x2: Real, x3: Real): Real = {
    require(x1.in(-15, 15) && x2.in(-15, 15) && x3.in(-15, 15) &&
            noise(x1, 1e-8) && noise(x2, 1e-8) && noise(x3, 1e-8))

    -x1*x2 - 2*x2*x3 - x1 - x3

  }

  def rigidBody1_1(x1: Real, x2: Real, x3: Real): Real = {
    require(x1.in(-15, 15) && x2.in(-15, 15) && x3.in(-15, 15) &&
            noise(x1, 1e-5) && noise(x2, 1e-7) && noise(x3, 1e-6))

    -x1*x2 - 2*x2*x3 - x1 - x3

  }

  def rigidBody2(x1: Real, x2: Real, x3: Real): Real = {
    require(x1.in(-15, 15) && x2.in(-15, 15) && x3.in(-15, 15) &&
            noise(x1, 1e-8) && noise(x2, 1e-8) && noise(x3, 1e-8))

    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2

  }

  def rigidBody2_1(x1: Real, x2: Real, x3: Real): Real = {
    require(x1.in(-15, 15) && x2.in(-15, 15) && x3.in(-15, 15) &&
            noise(x1, 1e-5) && noise(x2, 1e-7) && noise(x3, 1e-6))

    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2

  }

  def jetEngine(x1: Real, x2: Real): Real = {
    require(x1.in(-5, 5) && x2.in(-20, 5) && noise(x1, 1e-8) && noise(x2, 1e-8))

    val t = (3*x1*x1 + 2*x2 - x1)

    x1 + ((2*x1*(t/(x1*x1 + 1))*
    (t/(x1*x1 + 1) - 3) + x1*x1*(4*(t/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(t/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))

  }

  def jetEngine_1(x1: Real, x2: Real): Real = {
    require(x1.in(-5, 5) && x2.in(-20, 5) && noise(x1, 1e-10) && noise(x2, 1e-9))

    val t = (3*x1*x1 + 2*x2 - x1)

    x1 + ((2*x1*(t/(x1*x1 + 1))*
    (t/(x1*x1 + 1) - 3) + x1*x1*(4*(t/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(t/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))

  }

}
