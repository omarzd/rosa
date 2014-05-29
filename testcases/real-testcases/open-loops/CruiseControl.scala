import leon.real._
import RealOps._
import annotations._

object CruiseControl {


  @model
  def diffToSetPoint(oldDiff: Real): Real = {
    realValue 
  } ensuring( res => -1 <= res && res <= 1 && //&& res +/- 1e-5)/* &&
    -0.01 <= res - in && res - in <= 0.01)


  def control(oldError: Real, integral: Real, controlSignal: Real):
    (Real, Real, Real) = {

    val newError = diffToSetPoint(oldError)

    val dt = 0.1
    val newIntegral = integral + (newError * dt)

    val newDeriv = (newError - oldError) / 0.1

    val output = Kp * newError + Ki * newIntegral + Kd * newDeriv

    control(newError, newIntegral, output)
  }
}