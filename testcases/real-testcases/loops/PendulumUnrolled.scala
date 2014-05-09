import leon.real._
import RealOps._
import annotations._

object Pendulum {

  //m = 1, k = 2.3 => w = sqrt(2.3)
  @loopbound(10)
  def eulerP(theta: Real, omega: Real, i: Int): (Real, Real) = {
    require(loopCounter(i) && -2.0 <= theta && theta <= 2.0 &&
      -2.0 <= omega && omega <= 2.0 && -2.0 <= ~theta && ~theta <= 2.0 &&
      -2.0 <= ~omega && ~omega <= 2.0)// &&

    val theta1 = (theta + (0.1 * omega))
    val  omega1 =  (omega + (0.1 * (((((theta * theta) * theta) / 6.) - theta) - (0.1 * omega))))
    val  theta2 =  (theta1 + (0.1 * omega1))
    val  omega2 =  (omega1 + (0.1 * (((((theta1 * theta1) * theta1) / 6.) - theta1) - (0.1 * omega1))))
    val  theta3 =  (theta2 + (0.1 * omega2))
    val  omega3 =  (omega2 + (0.1 * (((((theta2 * theta2) * theta2) / 6.) - theta2) - (0.1 * omega2))))
    val  theta4 =  (theta3 + (0.1 * omega3))
    val  omega4 =  (omega3 + (0.1 * (((((theta3 * theta3) * theta3) / 6.) - theta3) - (0.1 * omega3))))
    val  theta5 =  (theta4 + (0.1 * omega4))
    val  omega5 =  (omega4 + (0.1 * (((((theta4 * theta4) * theta4) / 6.) - theta4) - (0.1 * omega4))))
    val  theta6 =  (theta5 + (0.1 * omega5))
    val  omega6 =  (omega5 + (0.1 * (((((theta5 * theta5) * theta5) / 6.) - theta5) - (0.1 * omega5))))
    val  theta7 =  (theta6 + (0.1 * omega6))
    val  omega7 =  (omega6 + (0.1 * (((((theta6 * theta6) * theta6) / 6.) - theta6) - (0.1 * omega6))))
    val  theta8 =  (theta7 + (0.1 * omega7))
    val  omega8 =  (omega7 + (0.1 * (((((theta7 * theta7) * theta7) / 6.) - theta7) - (0.1 * omega7))))
    val  theta9 =  (theta8 + (0.1 * omega8))
    val  omega9 =  (omega8 + (0.1 * (((((theta8 * theta8) * theta8) / 6.) - theta8) - (0.1 * omega8))))

    ((theta9 + (0.1 * omega9)), (omega9 + (0.1 * (((((theta9 * theta9) * theta9) / 6.) - theta9) - (0.1 * omega9)))))

  } ensuring (_ match {
    case (a, b) => -0.2 <= a && a <= 0.2 && -0.2 <= b && b <= 0.2 &&
      -0.2 <= ~a && ~a <= 0.2 && -0.2 <= ~b && ~b <= 0.2   
  })

}