import leon.real._
import RealOps._

object RigidBodyTestOut1 {


  def out0(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    ((((2.0 * (-x2 * x3)) + (-x1 * x2)) - x3) - x1)
  }

  def out1(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (((((2.0 * -x2) * x3) + (x1 * -x2)) - x3) - x1)
  }

  def out2(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (((-2.0 * x2) * x3) + ((x1 * -x2) + (-x1 - x3)))
  }

  def out3(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    ((((-2.0 * x3) * x2) + ((x1 * -x2) - x3)) - x1)
  }

  def out4(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (((2.0 * -(x2 * x3)) - (x1 + x3)) - (x1 * x2))
  }

  def out5(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    ((((2.0 * (x2 * -x3)) - x3) + (x1 * -x2)) - x1)
  }

  def out6(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    ((((-2.0 * x2) * x3) + (-x1 - (x1 * x2))) - x3)
  }

  def out7(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (((2.0 * -(x2 * x3)) + (-x1 - x3)) - (x1 * x2))
  }

  def out8(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (-((2.0 * x3) * x2) + (-x1 + ((-x1 * x2) - x3)))
  }

  def out9(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (((-(2.0 * (x2 * x3)) + (-x1 * x2)) - x3) - x1)
  }

  def out10(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (((((2.0 * -x2) * x3) + (-x1 * x2)) - x3) - x1)
  }

  def out11(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    ((-((2.0 * (x2 * x3)) + x1) - x3) + (-x1 * x2))
  }

  def out12(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    ((2.0 * -(x2 * x3)) + ((-x1 - (x1 * x2)) - x3))
  }

  def out13(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    ((((2.0 * x2) * -x3) + (-x1 + (x1 * -x2))) - x3)
  }

  def out14(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    ((((2.0 * -(x2 * x3)) - x3) - x1) + (-x1 * x2))
  }

  def out15(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (-((2.0 * x3) * x2) + ((-x1 + (-x1 * x2)) - x3))
  }

  def out16(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (((((2.0 * x2) * -x3) + (x1 * -x2)) - x1) - x3)
  }

  def out17(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (((2.0 * x2) * -x3) + ((-x1 - (x1 * x2)) - x3))
  }

  def out18(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    ((-((2.0 * (x2 * x3)) + x3) - x1) - (x1 * x2))
  }

  def out19(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (((((-2.0 * x2) * x3) - x1) - x3) + (x1 * -x2))
  }

  def out20(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    ((2.0 * (x2 * -x3)) + (-x1 + (-(x1 * x2) - x3)))
  }

  def out21(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    ((-(((2.0 * x2) * x3) + x1) + (x1 * -x2)) - x3)
  }
  def out22(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (((((2.0 * -x3) * x2) - x3) + (x1 * -x2)) - x1)
  }
  def out23(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    ((2.0 * -(x2 * x3)) + ((-x1 * x2) + (-x1 - x3)))
  }

  def out24(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (((-((2.0 * x3) * x2) - x3) - (x1 * x2)) - x1)
  }

  def out25(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    ((2.0 * (x2 * -x3)) + ((-x1 - (x1 * x2)) - x3))
  }

  def out26(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (((((2.0 * -x3) * x2) - x3) + (-x1 * x2)) - x1)
  }

  def out27(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (((2.0 * x2) * -x3) + (-(x1 * x2) + (-x1 - x3)))
  }

  def out28(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    ((-((2.0 * (x2 * x3)) + x1) - x3) - (x1 * x2))
  }

  def out29(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    ((((-2.0 * x2) * x3) + (-(x1 * x2) - x3)) - x1)
  }

  def out30(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    ((((2.0 * x2) * -x3) + (x1 * -x2)) + (-x1 - x3))
  }

  def out31(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (((-2.0 * x2) * x3) + (-x1 + ((-x1 * x2) - x3)))
  }

  def out32(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    ((-(2.0 * x3) * x2) + ((-x1 * x2) + (-x1 - x3)))
  }

  def out33(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (((-((2.0 * x3) * x2) - x3) - x1) - (x1 * x2))
  }

  def out34(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    ((-((2.0 * x2) * x3) - (x1 * x2)) + (-x1 - x3))
  }

  def out35(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (((((2.0 * -x2) * x3) - (x1 * x2)) - x3) - x1)
  }

  def out36(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    ((((2.0 * -x2) * x3) + ((x1 * -x2) - x3)) - x1)
  }

  def out37(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    ((((2.0 * (x2 * -x3)) + (x1 * -x2)) - x1) - x3)
  }

  def out38(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (((2.0 * -x2) * x3) + ((-x1 + (-x1 * x2)) - x3))
  }

  def out39(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    ((((2.0 * x2) * -x3) + (-x1 + (-x1 * x2))) - x3)
  }

  def out40(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (-((2.0 * x3) * x2) + ((-x1 * x2) + (-x1 - x3)))
  }

  def out41(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (((2.0 * -x2) * x3) + (-(x1 * x2) + (-x1 - x3)))
  }

  def out42(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (((2.0 * (-x2 * x3)) + (-x1 - x3)) + (x1 * -x2))
  }

  def out43(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (((2.0 * (-x2 * x3)) - (x1 * x2)) + (-x1 - x3))
  }

  def out44(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (((-(2.0 * x2) * x3) + ((-x1 * x2) - x3)) - x1)
  }

  def out45(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (((2.0 * (-x2 * x3)) + (x1 * -x2)) - (x1 + x3))
  }

  def out46(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    ((((2.0 * -(x2 * x3)) + (-x1 * x2)) - x1) - x3)
  }

  def out47(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    ((((2.0 * (x2 * -x3)) - x1) - x3) + (x1 * -x2))
  }

  def out48(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (((((-2.0 * x3) * x2) + (-x1 * x2)) - x3) - x1)
  }

  def out49(x1: Real, x2: Real, x3: Real): Real = {
    require(-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15)
    (((2.0 * -(x2 * x3)) - (x1 * x2)) - (x1 + x3))
  }

  
}