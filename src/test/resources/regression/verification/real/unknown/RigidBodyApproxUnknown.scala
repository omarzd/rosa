/* Copyright 2009-2014 EPFL, Lausanne */
import leon.real._
import RealOps._

object RigidBodyApproxUnknown {

  def rigidBody1Star(x1: Real, x2: Real, x3: Real): Real = {
    require(-15.0 <= x1 && x1 <= 15 && -15.0 <= x2 && x2 <= 15.0 && -15.0 <= x3 && x3 <= 15 &&
      x1 +/- 1e-8 && x2 +/- 1e-8 && x3 +/- 1e-8)
    -x1*x2 - 2*x2*x3 - x1 - x3
  } ensuring(res => -705.0 <= res && res <= 705.0 && res +/- 9.2e-7)

  def rigidBody1_3(x1: Real, x2: Real, x3: Real): Real = {
    require(-15.0 <= x1 && x1 <= 15 && -15.0 <= x2 && x2 <= 15.0 && -15.0 <= x3 && x3 <= 15)

    -x1*x2 - 2*x2*x3 - x1 - x3
  } ensuring(res => -705.0 <= res && res <= 705.0 && res +/- 3.2152e-13)


  def rigidBody2Star(x1: Real, x2: Real, x3: Real): Real = {
    require(-15.0 <= x1 && x1 <= 15 && -15.0 <= x2 && x2 <= 15.0 && -15.0 <= x3 && x3 <= 15 &&
      x1 +/- 1e-8 && x2 +/- 1e-8 && x3 +/- 1e-8)

    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  } ensuring(res => -56010.0001 <= res && res <= 58740.0 && res +/- 0.0001503)

  def rigidBody2_3(x1: Real, x2: Real, x3: Real): Real = {
    require(-15.0 <= x1 && x1 <= 15 && -15.0 <= x2 && x2 <= 15.0 && -15.0 <= x3 && x3 <= 15)

    2*x1*x2*x3 + 3*x3*x3 - x2*x1*x2*x3 + 3*x3*x3 - x2
  } ensuring(res => -56010.0001 <= res && res <= 58740.0 && res +/- 3.6465e-11)

}