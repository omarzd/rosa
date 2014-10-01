import leon.real._
import RealOps._
import annotations._

object BicycleControl {

  @model
  def getInput(in: Real): Real = {
    realValue 
  } ensuring( res => -1 <= res && res <= 1 && //&& res +/- 1e-5)/* &&
    -0.01 <= res - in && res - in <= 0.01)

  @loopbound(100)
  def control(s1: Real, s2: Real, t: Int, oldIn: Real): (Real, Real) = {
    require(-1 <= s1 && s1 <= 1 && -1 <= s2 && s2 <= 1 && loopCounter(t) &&
      -1 <= oldIn && oldIn <= 1) //initialError(s, 1e-6)

    if (t <= 100) {
      val in = getInput(oldIn)
      
      val s1New = (0.961270) * s1 + (-0.095962) * s2 + (0.013200) * in
      val s2New = (-0.058217) * s1 + (0.727430) * s2 + (0.102100) * in
      //val out = (-3.025300) * s1 + (-12.608900) * s2
      //assert( .. sth about out .. )
      control(s1New, s2New, t + 1, in)
    } else {
      (s1, s2)      
    }

  } ensuring (_ match {
    case (s1New, s2New) =>
      -1 <= s1New && s1New <= 1 && -1 <= s2New && s2New <= 1 &&
      -1 <= ~s1New && ~s1New <= 1 && -1 <= ~s2New && ~s2New <= 1      
    })





  /*def bicycle(s1: Real, s2: Real, in: Real): (Real, Real, Real) = {
    require(-1 <= s1 && s1 <= 1 && -1 <= s2 && s2 <= 1 &&
      -1 <= in && in <= 1)

    val s1New = (0.961270) * s1 + (-0.095962) * s2 + (0.013200) * in
    val s2New = (-0.058217) * s1 + (0.727430) * s2 + (0.102100) * in
    val out = (-3.025300) * s1 + (-12.608900) * s2

    (s1New, s2New, out)
  } ensuring (_ match {
    case (s1New, s2New, out) =>
      -1 <= s1New && s1New <= 1 && -1 <= s2New && s2New <= 1 &&
      -1 <= ~s1New && ~s1New <= 1 && -1 <= ~s2New && ~s2New <= 1      
    })
  */
}