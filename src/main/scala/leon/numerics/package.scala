package leon

import ceres.common.{DirectedRounding}
import numerics.affine.Rational
import java.math.{BigInteger}


package object numerics {

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

  case class UnsupportedFragmentException(msg: String) extends Exception(msg)

  object ApproximationType extends Enumeration {
    type ApproximationType = Value
    val Uninterpreted_None = Value("Uninterpreted_None")
    val PostInlining_None = Value("PostInlining_None")
    val FullInlining_None = Value("FullInlining_None")
    val NoFncs_AA = Value("NoFncs_AA")
    val NoFncs_AAMerging = Value("NoFncs_AAMerging")
    val FullInlining_AA = Value("FullInlining_AA")
    val FullInlining_AAMerging = Value("FullInlining_AAMerging")
    //val PostInlining_AA = Value("PostInlining_AA")
    //val PostInlining_AAMerging = Value("PostInlining_AAMerging")
  }

  object RoundoffType extends Enumeration {
    type RoundoffType = Value
    val NoRoundoff = Value("NoRoundoff")
    val RoundoffMultiplier = Value("RndoffMultiplier")
    val RoundoffAddition = Value("RndoffAddition")
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
