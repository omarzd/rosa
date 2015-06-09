/* Copyright 2009-2015 EPFL, Lausanne */

package leon

import purescala.Trees._
import purescala.Common._


import ceres.common.{DirectedRounding}



package object real {

  val True = BooleanLiteral(true)
  val False = BooleanLiteral(false)

  val DummySpec = SimpleSpec(FreshIdentifier("dummyResult"),
    RationalInterval(Rational.zero, Rational.zero), Some(Rational.zero))

  val useMassageArithmetic = true

  case class UnsupportedRealFragmentException(msg: String) extends Exception(msg)
  case class RealArithmeticException(msg: String) extends Exception(msg)
  case class PostconditionInliningFailedException(msg: String) extends Exception(msg)
  case class UnsoundBoundsException(msg: String) extends Exception(msg)

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
  

  object Sat extends Enumeration {
    type Sat = Value
    val SAT = Value("SAT")
    val UNSAT = Value("UNSAT")
    val Unknown = Value("Unknown")
  }

  object Status extends Enumeration {
    type Status = Value
    val VALID = Value("VALID")
    val INVALID = Value("INVALID")
    val UNKNOWN = Value("Unknown")
    val NothingToShow = Value("n/a")
    val ERROR = Value("Error")
  }
}
