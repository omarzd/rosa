
import leon.Real
import Real._


/**
  These benchmarks come from the fixed-point arithmetic domain.
 */
object FixedpointSpecGen {

  // Sim: [-1778.572314073148,4809.339509539625]    (4.547473508864641E-12)
  def jetEngine(x1: Real, x2: Real): Real = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5 && roundoff(x1) && roundoff(x2))
    x1 + ((2*x1*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1))*
    ((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1) - 3) + x1*x1*(4*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  }

  //((-1780.3677909661192 ≤ #res) ∧ (#res ≤ 4820.019826362952) ∧ noise(#res,3.1164389513739606E-8))


  // Sim: [-693.0980449078490,687.4198314598049]    (2.2737367544323206E-13)
  def rigidBody1(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 15 && x1 >= -15 && x2 <= 15 && x2 >= -15 &&
            x3 <= 15 && x3 >= -15 && roundoff(x1) && roundoff(x2) && roundoff(x3))
    -x1*x2 - 2*x2*x3 - x1 - x3
  }

  // ((-705.0000000000005 ≤ #res) ∧ (#res ≤ 705.0000000000005) ∧ noise(#res,5.079270570002227E-13))

  // Sim: [-2638.451636347363,2756.816301997386]    (9.094947017729282E-13)
  def rigidBody1_2(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 13 && x1 >= -20 && x2 <= 25 && x2 >= -25 &&
            x3 <= 35 && x3 >= -45 && roundoff(x1) && roundoff(x2) && roundoff(x3))
    -x1*x2 - 2*x2*x3 - x1 - x3
  }

  // ((-2685.0013966560387 ≤ #res) ∧ (#res ≤ 2815.0000000000023) ∧ noise(#res,2.0983222245270748E-12))

  // Sim: [-1142.038583258746,622.6370473435335]    (4.547473508864641E-13)
  def rigidBody1_3(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 20 && x1 >= -10 && x2 <= 10 && x2 >= -20 &&
            x3 <= 5 && x3 >= -25 && roundoff(x1) && roundoff(x2) && roundoff(x3))
    -x1*x2 - 2*x2*x3 - x1 - x3
  }

  //((-1165.000000000001 ≤ #res) ∧ (#res ≤ 635.000443458558) ∧ noise(#res,9.447999323619815E-13))

  // Sim: [-53914.95897764155,57835.66271360889]    (2.1827872842550278E-11)
  def rigidBody2(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 15 && x1 >= -15 && x2 <= 15 && x2 >= -15 &&
            x3 <= 15 && x3 >= -15 && roundoff(x1) && roundoff(x2) && roundoff(x3))
    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  }

  //((-56010.05252838141 ≤ #res) ∧ (#res ≤ 58740.000000000065) ∧ noise(#res,6.475183068501535E-11))

  // Sim: [-564937.4996816926,471323.6113501612]    (2.3283064365386963E-10)
  def rigidBody2_2(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 13 && x1 >= -20 && x2 <= 25 && x2 >= -25 &&
            x3 <= 35 && x3 >= -45 && roundoff(x1) && roundoff(x2) && roundoff(x3))
    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  }

  // ((-595325.5225300796 ≤ #res) ∧ (#res ≤ 479875.3239929683) ∧ noise(#res,6.765845112203587E-10))

  // Sim: [-100418.7322517922,221185.3529955959]    (8.731149137020111E-11)
  def rigidBody2_3(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 20 && x1 >= -10 && x2 <= 10 && x2 >= -20 &&
            x3 <= 5 && x3 >= -25 && roundoff(x1) && roundoff(x2) && roundoff(x3))
    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  }

  //((-106230.03521919275 ≤ #res) ∧ (#res ≤ 223770.00000000023) ∧ noise(#res,2.471747535123445E-10))


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
