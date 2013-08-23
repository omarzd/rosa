/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import leon.purescala.Trees._
import leon.purescala.Definitions._
import leon.purescala.Common._

import Precision._


case class Spec(bounds: RationalInterval, absError: Rational)

object VerificationCondition {
  val initialValueMap = Map(Float32 -> None, Float64 -> None, DoubleDouble -> None, QuadDouble -> None)
}

// The condition is pre => post
class VerificationCondition(val funDef: FunDef, val kind: VCKind.Value, val pre: Expr, val body: Expr,  
  val post: Expr, val variables: VariablePool) extends ScalacPositional {
  import VerificationCondition._

  var allFncCalls = Set[String]()

  // FIXME: id is bad here, not unique
  val id = funDef.id.toString

  //var realFncBody: Expr = True

  // (lowerBnd, upperBnd) absError
  var spec: Map[Precision, Option[Spec]] = initialValueMap

  // None = still unknown
  // Some(true) = valid
  // Some(false) = invalid
  var value: Map[Precision, Option[Boolean]] = initialValueMap

  def this(fD: FunDef, k:VCKind.Value, pe: Expr, b: Expr, po: Expr, fncCalls: Set[String], vars: VariablePool) = {
    this(fD, k, pe, b, po, vars)
    allFncCalls = fncCalls
  }


  def status(precision: Precision) : String = value(precision) match {
    case None => "unknown"
    case Some(true) => "valid"
    case Some(false) => "invalid"
  }



  var time : Option[Double] = None
  var counterExample : Option[Map[Identifier, Expr]] = None
}

object VCKind extends Enumeration {
  val Precondition = Value("precond.")
  val Postcondition = Value("postcond.")
  val Assertion = Value("assert.")
}