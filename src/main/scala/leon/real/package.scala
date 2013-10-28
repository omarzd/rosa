/* Copyright 2013 EPFL, Lausanne */

package leon

import purescala.Trees._

import ceres.common.{DirectedRounding}
import java.math.{BigInteger}

package object real {

  val True = BooleanLiteral(true)
  val False = BooleanLiteral(false)

  val useMassageArithmetic = true

  case class UnsupportedRealFragmentException(msg: String) extends Exception(msg)
  case class RealArithmeticException(msg: String) extends Exception(msg)
  case class PostconditionInliningFailedException(msg: String) extends Exception(msg)
  case class UnsoundBoundsException(msg: String) extends Exception(msg)

  case class Fnc(pre: Expr, body: Expr, post: Expr)

  case class Path(condition: Expr, body: Expr)


  def formatOption[T](res: Option[T]): String = res match {
    case Some(xf) => xf.toString
    case None => " -- "
  }

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
  def isExact(r: Rational): Boolean = r.isWhole

  
  object Sat extends Enumeration {
    type Sat = Value
    val SAT = Value("SAT")
    val UNSAT = Value("UNSAT")
    val Unknown = Value("Unknown")
  }
}