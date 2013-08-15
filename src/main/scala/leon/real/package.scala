package leon


package object real {

  case class UnsupportedRealFragmentException(msg: String) extends Exception(msg)

  object Precision extends Enumeration {
    type Precision = Value
    val Float64 = Value("Float64")
    val Float32 = Value("Float32")
    val DoubleDouble = Value("DoubleDouble")
    val QuadDouble = Value("QuadDouble")
  }
  import Precision._

  class RealOptions {
    var simulation = false
    var z3Timeout = 1000l
    var precision: List[Precision] = List(Float64)
    var z3Only = false
    var pathSensitive = false
    var specGen = true

    override def toString: String = "simulation: %s,\nz3 timeout: %s,\nprecision: %s,\nz3Only: %s,\npathSensitive: %s,\nspecGen: %s".format(
      simulation, z3Timeout, precision, z3Only, pathSensitive, specGen) 
  }

  
}