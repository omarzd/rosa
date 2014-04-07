import leon.real._
import RealOps._
import annotations._

object Controller {

  @model
  def getInput(in: Real): Real = {
    realValue 
  } ensuring( res => -1 <= res && res <= 1 &&
    -0.01 <= res - in && res - in <= 0.01)

  def control(s: Real, t: Int, oldInput: Real): Real = {
    require(initialError(s, 1e-6) && -1 <= s && s <= 1 && loopCounter(t))

    if (t > 100) {
      s
    } else {
      val in = getInput(oldInput)
      val sNew = f(s, )
      control(sNew, t + 1, in)
    }

  } ensuring (res =>
    )

}