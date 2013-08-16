/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import leon.purescala.Trees._
import leon.purescala.Definitions._
import leon.purescala.Common._

// The condition is pre => post
class VerificationCondition(val funDef: FunDef, val kind: VCKind.Value, val pre: Expr, val body: Expr,
  val post: Expr) extends ScalacPositional {
  var allFncCalls = Set[String]()

  val id = funDef.id.toString

  // None = still unknown
  // Some(true) = valid
  // Some(false) = valid
  var value : Option[Boolean] = None

  def this(fD: FunDef, k:VCKind.Value, pe: Expr, b: Expr, po: Expr, fncCalls: Set[String]) = {
    this(fD, k, pe, b, po)
    allFncCalls = fncCalls
  }

  
  def status : String = value match {
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