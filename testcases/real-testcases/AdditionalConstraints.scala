
// Enable using of additional constraints on the variables
// during range determination.
// I.e. pass on the constraints to XFloat and Z3
object AdditionalConstraints {

  def fnc1(x: Double, y: Double): Double = {
    require(x < y)

  }

}
