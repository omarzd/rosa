package leon

import purescala.Trees._

import ceres.common.{DirectedRounding}
import java.math.{BigInteger}

package object real {

  val True = BooleanLiteral(true)
  val False = BooleanLiteral(false)

  case class UnsupportedRealFragmentException(msg: String) extends Exception(msg)

  object Precision extends Enumeration {
    type Precision = Value
    val Float64 = Value("Float64")
    val Float32 = Value("Float32")
    val DoubleDouble = Value("DoubleDouble")
    val QuadDouble = Value("QuadDouble")
  }
  import Precision._

  def getUnitRoundoff(precision: Precision): Rational = precision match {
    case Float32 => Rational(new BigInt(new BigInteger("1")), new BigInt(new BigInteger("2")).pow(23))
    case Float64 => Rational(new BigInt(new BigInteger("1")), new BigInt(new BigInteger("2")).pow(53))
    case DoubleDouble => Rational(new BigInt(new BigInteger("1")), new BigInt(new BigInteger("2")).pow(105))
    case QuadDouble => Rational(new BigInt(new BigInteger("1")), new BigInt(new BigInteger("2")).pow(211))
  }

  val solverPrecisionHigh = Rational.rationalFromReal(1e-16)
  val solverPrecisionMedium = Rational.rationalFromReal(1e-10)
  val solverPrecisionLow = Rational.rationalFromReal(1e-5)

  val solverMaxIterHigh = 70
  val solverMaxIterMedium = 50
  val solverMaxIterLow = 20

  // Tests whether this rational can be represented without roundoff errors
  // Since we don't know which precision we may test, returns, for now, true only for integers
  def isExact(r: Rational): Boolean = {
    r.isWhole
  }

  class RealOptions {
    var simulation = false
    var z3Timeout = 1000l
    var precision: List[Precision] = List(Float64)
    var z3Only = false
    var pathSensitive = false
    var specGen = true
    var solverMaxIter = solverMaxIterMedium
    var solverPrecision = solverPrecisionMedium

    override def toString: String = "simulation: %s,\nz3 timeout: %s,\nprecision: %s,\nz3Only: %s,\npathSensitive: %s,\nspecGen: %s".format(
      simulation, z3Timeout, precision, z3Only, pathSensitive, specGen) 
  }

  object Sat extends Enumeration {
    type Sat = Value
    val SAT = Value("SAT")
    val UNSAT = Value("UNSAT")
    val Unknown = Value("Unknown")
  }

  object Valid extends Enumeration {
    type Valid = Value
    val VALID = Value("VALID")
    val INVALID = Value("INVALID")
    val UNKNOWN = Value("Not sure")
  }
}