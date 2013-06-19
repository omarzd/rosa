package leon

import ceres.common.{Rational, DirectedRounding}
import java.math.{BigInteger}


package object numerics {

  object Precision extends Enumeration {
    type Precision = Value
    val Float64 = Value("Float64")
    val Float32 = Value("Float32")
  }
  import Precision._

  def getUnitRoundoff(precision: Precision): Rational = precision match {
    case Float32 => Rational(new BigInt(new BigInteger("1")), new BigInt(new BigInteger("2")).pow(23))
    case Float64 => Rational(new BigInt(new BigInteger("1")), new BigInt(new BigInteger("2")).pow(53))
  }


  case class UnsupportedFragmentException(msg: String) extends Exception(msg)

  object ApproximationType extends Enumeration {
    type ApproximationType = Value
    val Uninterpreted_None = Value("Uninterpreted_None")
    val PostInlining_None = Value("PostInlining_None")
    val PostInlining_AA = Value("PostInlining_AA")
    val FullInlining_None = Value("FullInlining_None")
    val FullInlining_AA = Value("FullInlining_AA")
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
    val NOT_SURE = Value("Not sure")  //computed range may be too large
    val DUNNO = Value("Unknown")  //Z3 failed or something like that
  }

}
