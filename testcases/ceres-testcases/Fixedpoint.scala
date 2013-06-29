
import leon.Real
import Real._


/**
  These benchmarks come from the fixed-point aritmetic domain.
 */
object Fixedpoint {

  // Sim: [-693.0980449078490,687.4198314598049]    (2.2737367544323206E-13)
  def rigidBody1Invalid(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 15 && x1 >= -15 && x2 <= 15 && x2 >= -15 &&
            x3 <= 15 && x3 >= -15)
    -x1*x2 - 2*x2*x3 - x1 - x3
  } ensuring (res => -694 <= res && res <= 688.0 && noise(res, 1e-12))

  def rigidBody1(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 15 && x1 >= -15 && x2 <= 15 && x2 >= -15 &&
            x3 <= 15 && x3 >= -15)
    -x1*x2 - 2*x2*x3 - x1 - x3
  } ensuring (res => -800 <= res && res <= 750.0 && noise(res, 1e-10))

  // Sim: [-2638.451636347363,2756.816301997386]    (9.094947017729282E-13)
  def rigidBody1_2Invalid(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 13 && x1 >= -20 && x2 <= 25 && x2 >= -25 &&
            x3 <= 35 && x3 >= -45)
    -x1*x2 - 2*x2*x3 - x1 - x3
  } ensuring (res => -2640.0 <= res && res <= 2760.0 && noise(res, 1e-12))

  def rigidBody1_2(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 13 && x1 >= -20 && x2 <= 25 && x2 >= -25 &&
            x3 <= 35 && x3 >= -45)
    -x1*x2 - 2*x2*x3 - x1 - x3
  } ensuring (res => -2850.0 <= res && res <= 2950.0 && noise(res, 1e-9))

  // Sim: [-1142.038583258746,622.6370473435335]    (4.547473508864641E-13)
  def rigidBody1_3(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 20 && x1 >= -10 && x2 <= 10 && x2 >= -20 &&
            x3 <= 5 && x3 >= -25)
    -x1*x2 - 2*x2*x3 - x1 - x3
  } ensuring (res => -1300.0 <= res && res <= 750.0 && noise(res, 1e-9))

  // Sim: [-53914.95897764155,57835.66271360889]    (2.1827872842550278E-11)
  def rigidBody2Invalid(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 15 && x1 >= -15 && x2 <= 15 && x2 >= -15 &&
            x3 <= 15 && x3 >= -15)
    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  } ensuring (res => -53920.0 <= res && res >= 57840.0 && noise(res, 1e-10))
  
  def rigidBody2(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 15 && x1 >= -15 && x2 <= 15 && x2 >= -15 &&
            x3 <= 15 && x3 >= -15)
    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  } ensuring (res => -55500.0 <= res && res >= 59500.0 && noise(res, 1e-8))
   
  // Sim: [-564937.4996816926,471323.6113501612]    (2.3283064365386963E-10)
  def rigidBody2_2Invalid(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 13 && x1 >= -20 && x2 <= 25 && x2 >= -25 &&
            x3 <= 35 && x3 >= -45)
    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  } ensuring (res => -565000.0 <= res && res >= 472000.0 && noise(res, 1e-9))

  def rigidBody2_2(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 13 && x1 >= -20 && x2 <= 25 && x2 >= -25 &&
            x3 <= 35 && x3 >= -45)
    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  } ensuring (res => -650000.0 <= res && res >= 550000.0 && noise(res, 1e-4))

  // Sim: [-100418.7322517922,221185.3529955959]    (8.731149137020111E-11)
  def rigidBody2_3Invalid(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 20 && x1 >= -10 && x2 <= 10 && x2 >= -20 &&
            x3 <= 5 && x3 >= -25)
    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  } ensuring (res => -101000.0 <= res && res >= 222000.0 && noise(res, 1e-10))

  def rigidBody2_3(x1: Real, x2: Real, x3: Real): Real = {
    require(x1 <= 20 && x1 >= -10 && x2 <= 10 && x2 >= -20 &&
            x3 <= 5 && x3 >= -25)
    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  } ensuring (res => -125000.0 <= res && res >= 245000.0 && noise(res, 1e-9))


  // Sim: [-1778.572314073148,4809.339509539625]    (4.547473508864641E-12)
  def jetEngine(x1: Real, x2: Real): Real = {
    require(-5 <= x1 && x1 <= 5 && -20 <= x2 && x2 <= 5)
    x1 + ((2*x1*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1))*
    ((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1) - 3) + x1*x1*(4*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*((3*x1*x1 + 2*x2 - x1)/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)))
  } ensuring (res => -2500.0 <= res && res >= 5500.0 && noise(res, 1e-10))

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
