
import leon.Real
import Real._


/**
  These benchmarks come from the fixed-point aritmetic domain.
 */
object FixedpointSpecGen {

  // Sim: [-693.0980449078490,687.4198314598049]    (2.2737367544323206E-13)
  def rigidBody1(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 15 && x1 >= -15 && x2 <= 15 && x2 >= -15 &&
            x3 <= 15 && x3 >= -15 && roundoff(x1) && roundoff(x2) && roundoff(x3))
    -x1*x2 - 2*x2*x3 - x1 - x3
  }

  // Sim: [-2638.451636347363,2756.816301997386]    (9.094947017729282E-13)
  def rigidBody1_2(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 13 && x1 >= -20 && x2 <= 25 && x2 >= -25 &&
            x3 <= 35 && x3 >= -45 && roundoff(x1) && roundoff(x2) && roundoff(x3))
    -x1*x2 - 2*x2*x3 - x1 - x3
  }

  // Sim: [-1142.038583258746,622.6370473435335]    (4.547473508864641E-13)
  def rigidBody1_3(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 20 && x1 >= -10 && x2 <= 10 && x2 >= -20 &&
            x3 <= 5 && x3 >= -25 && roundoff(x1) && roundoff(x2) && roundoff(x3))
    -x1*x2 - 2*x2*x3 - x1 - x3
  }

  // Sim: [-53914.95897764155,57835.66271360889]    (2.1827872842550278E-11)
  def rigidBody2(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 15 && x1 >= -15 && x2 <= 15 && x2 >= -15 &&
            x3 <= 15 && x3 >= -15 && roundoff(x1) && roundoff(x2) && roundoff(x3))
    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  }

  // Sim: [-564937.4996816926,471323.6113501612]    (2.3283064365386963E-10)
  def rigidBody2_2(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 13 && x1 >= -20 && x2 <= 25 && x2 >= -25 &&
            x3 <= 35 && x3 >= -45 && roundoff(x1) && roundoff(x2) && roundoff(x3))
    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  }

  // Sim: [-100418.7322517922,221185.3529955959]    (8.731149137020111E-11)
  def rigidBody2_3(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 20 && x1 >= -10 && x2 <= 10 && x2 >= -20 &&
            x3 <= 5 && x3 >= -25 && roundoff(x1) && roundoff(x2) && roundoff(x3))
    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  }

  // Sim: [-1778.572314073148,4809.339509539625]    (4.547473508864641E-12)
  def jetEngine(x1: Real, x2: Real): Real = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5 && roundoff(x1) && roundoff(x2))
    x1 + ((2*x1*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1))*
    ((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1) - 3) + x1*x1*(4*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  }

  // Possible division by zero
/*  def jetEngine2(x1: Real, x2: Real): Real = {
    require(-7 <= x1 && x1 <= 15 && -25 <= x2 && x2 <= 15)
    x1 + ((2*x1*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1))*
    ((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1) - 3) + x1*x1*(4*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  } ensuring (res => res >= -32000.0)

  def jetEngine3(x1: Real, x2: Real): Real = {
    require(0 <= x1 && x1 <= 10 && -10 <= x2 && x2 <= 20)
    x1 + ((2*x1*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1))*
    ((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1) - 3) + x1*x1*(4*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  } ensuring (res => res >= -32000.0)
*/


}
