package leon

import ceres.common.{Rational, DirectedRounding}
import java.math.{BigInteger}


package object numerics {

  val unitRndoff = Rational(new BigInt(new BigInteger("1")),
    new BigInt(new BigInteger("2")).pow(53))
  //val unitRndoff = Rational(new BigInt(new BigInteger("1")),
  //  new BigInt(new BigInteger("2")).pow(23))

  case class UnsupportedFragmentException(msg: String) extends Exception(msg)

  // Until we get this sorted in Rational
  def sqrtUp(x: Rational): Rational = Rational(math.sqrt(Rational.scaleToIntsUp(x).doubleValue))
  def sqrtDown(x: Rational): Rational = Rational(math.sqrt(Rational.scaleToIntsDown(x).doubleValue))

  object RoundoffType extends Enumeration {
    type RoundoffType = Value
    val NoRoundoff = Value("NoRoundoff")
    val RoundoffMultiplier = Value("RndoffMultiplier")
    val RoundoffAddition = Value("RndoffAddition")
  }

  object Precision extends Enumeration {
    type Precision = Value
    val Float64 = Value("Float64")
    val Float32 = Value("Float32")
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
