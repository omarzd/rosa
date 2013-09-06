package leon

import purescala.Trees._

import ceres.common.{DirectedRounding}
import java.math.{BigInteger}

package object real {

  val True = BooleanLiteral(true)
  val False = BooleanLiteral(false)

  case class UnsupportedRealFragmentException(msg: String) extends Exception(msg)
  case class ArithmeticException(msg: String) extends Exception(msg)
  case class FixedPointOverflowException(s: String) extends Exception
  case class IncompatibleFixedPointFormatsException(s: String) extends Exception
  

  case class Fnc(pre: Expr, body: Expr, post: Expr)

  case class Path(condition: Expr, body: Expr)

  case class ApproxKind(fncHandling: FncHandling.Value, pathHandling: PathHandling.Value, arithmApprox: ArithmApprox.Value)

  case class Approximation(kind: ApproxKind, cnstrs: Seq[Expr], sanityChecks: Seq[Expr], spec: Option[Spec])

  def formatOption[T](res: Option[T]): String = res match {
    case Some(xf) => xf.toString
    case None => " -- "
  }

  def printFloat(f: Double): String = {
    if (f >= 1.0) "%.6f".format(f)
    else if (f >= 0.001) "%.9f".format(f)
    else if (f >= 0.00001) "%.12f".format(f)
    else "%.16f".format(f)
  }

  sealed abstract class Precision
  object Float64 extends Precision // = Value("Float64")
  object Float32 extends Precision //= Value("Float32")
  object DoubleDouble extends Precision //= Value("DoubleDouble")
  object QuadDouble extends Precision //= Value("QuadDouble")
  case class FPPrecision(bitlength: Int) extends Precision
  //import Precision._

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
  def isExact(r: Rational): Boolean = r.isWhole

  class RealOptions {
    var simulation = false
    var z3Timeout = 1000l
    var precision: List[Precision] = List(Float64)
    var z3Only = false
    var pathSensitive = false
    var solverMaxIter = solverMaxIterMedium
    var solverPrecision = solverPrecisionMedium

    override def toString: String = "simulation: %s,\nz3 timeout: %s,\nprecision: %s,\nz3Only: %s,\npathSensitive: %s".format(
      simulation, z3Timeout, precision, z3Only, pathSensitive)
  }

  object FncHandling extends Enumeration {
    type FncHandling = Value
    val Uninterpreted = Value("Uninterpreted")
    val Postcondition = Value("Postcondition")
    val Inlining = Value("Inlining")
  }

  object PathHandling extends Enumeration {
    type PathHandling = Value
    val Pathwise = Value("Pathwise")
    val Merging = Value("Merging")
  }

  object ArithmApprox extends Enumeration {
    type ArithmApprox = Value
    val Z3Only = Value("Z3Only")
    val JustFloat = Value("JustFloat") // evaluate the float. part with xfloat
    val FloatNRange = Value("Float'n'Range") // also replace the real with an approx. of the range
  }

  object Sat extends Enumeration {
    type Sat = Value
    val SAT = Value("SAT")
    val UNSAT = Value("UNSAT")
    val Unknown = Value("Unknown")
  }
}