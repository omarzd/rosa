package leon
package numerics

import ceres.common._

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import Valid._
import Utils._


// It's one for each method, but may store several conditions to be proven.
class VerificationCondition(val funDef: FunDef) {

  // Info the user must have provided (for now)
  var inputs: Map[Variable, Record] = Map.empty
  var precondition: Option[Expr] = None

  // pre and body
  var preConstraint: Option[Expr] = None
  var bodyConstraint: Option[Expr] = None
  var postConstraint: Option[Expr] = None

  /*
    Constraints needed to prove.
    WR: With Roundoff, RA: Real Arithmetic only
  */
  var toCheck: List[Constraint] = List.empty

  /*var fncConstraintWR: Option[Expr] = None
  var statusWR: (Option[Valid], Option[z3.scala.Z3Model]) = (None, None)

  var fncConstraintRA: Option[Expr] = None
  var statusRA: (Option[Valid], Option[z3.scala.Z3Model]) = (None, None)
  */

  /*
    Computed specification.
  */
  //var inferredPost: Option[Expr] = None


  /*
    Runtime specification.
  */
  //var runtimePre: Option[Expr] = None
  //var runtimePost: Option[Expr] = None


  /* Some stats */
  var analysisTime: Option[Long] = None
  var verificationTime:Option[Long] = None
}


case class Constraint(pre: Expr, body: Expr, post: Expr) {
  var status: Option[Valid] = None
  var model: Option[Map[Identifier, Expr]] = None

  def numVariables: Int = variablesOf(pre).size + variablesOf(body).size
  def size: Int = formulaSize(pre) + formulaSize(body)

}
