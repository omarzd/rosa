/* Copyright 2013 EPFL, Lausanne */

package leon

import purescala.Trees._

import ceres.common.{DirectedRounding}
import java.math.{BigInteger}

package object real {

  val True = BooleanLiteral(true)
  val False = BooleanLiteral(false)

  val DummySpec = Spec(RationalInterval(Rational.zero, Rational.zero), Rational.zero)

  val useMassageArithmetic = true

  case class UnsupportedRealFragmentException(msg: String) extends Exception(msg)
  case class RealArithmeticException(msg: String) extends Exception(msg)
  case class PostconditionInliningFailedException(msg: String) extends Exception(msg)
  case class UnsoundBoundsException(msg: String) extends Exception(msg)

  // TODO: check if we need this one
  case class ArithmeticException(msg: String) extends Exception(msg)
  case class FixedPointOverflowException(s: String) extends Exception
  case class IncompatibleFixedPointFormatsException(s: String) extends Exception
  

  case class Fnc(pre: Expr, body: Expr, post: Expr)

  case class Path(condition: Expr, bodyReal: Expr, bodyFinite: Expr)


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
  case object Float64 extends Precision // = Value("Float64")
  case object Float32 extends Precision //= Value("Float32")
  case object DoubleDouble extends Precision //= Value("DoubleDouble")
  case object QuadDouble extends Precision //= Value("QuadDouble")
  case class FPPrecision(bitlength: Int) extends Precision
  //import Precision._

  def getUnitRoundoff(precision: Precision): Rational = (precision: @unchecked) match {
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

  object Sat extends Enumeration {
    type Sat = Value
    val SAT = Value("SAT")
    val UNSAT = Value("UNSAT")
    val Unknown = Value("Unknown")
  }
}