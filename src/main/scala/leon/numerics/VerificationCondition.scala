package leon
package numerics

import ceres.common._

import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import Valid._


// It's one for each method, but may store several conditions to be proven.
class VerificationCondition(val funDef: FunDef) {

  /*
    Whole function constraints. These are the ones we ultimately need to prove.
    WR: With Roundoff
    RA: Real Arithmetic only
  */
  var fncConstraintWR: Option[Expr] = None
  var statusWR: (Option[Valid], Option[z3.scala.Z3Model]) = (None, None)

  var fncConstraintRA: Option[Expr] = None
  var statusRA: (Option[Valid], Option[z3.scala.Z3Model]) = (None, None)

  
  /*
    Complete specification.
    If the method has a postcondition already, we use it (for now).
    We may also want to strenghten it (at some point).
    Currently, each method needs to specify all input ranges completely.
    We may want to infer those from calling methods at some point.
  */
  // Keep a variable which is hopefully already typed. Saves maybe a few crashes.
  var inputRanges: Map[Variable, RationalInterval] = Map.empty
  var precondition: Option[Expr] = None
  var postcondition: Option[Expr] = None

  /*
    Runtime specification.
  */
  var runtimePre: Option[Expr] = None
  var runtimePost: Option[Expr] = None


  /* Some stats */
  var constraintGenTime: Option[Long] = None
}
