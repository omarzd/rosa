package leon
package numerics

import ceres.common._
import ceres.smartfloat._

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import Valid._
import Utils._


// It's one for each method, but may store several conditions to be proven.
class VerificationCondition(val funDef: FunDef) {


  var inputs: Map[Variable, Record] = Map.empty
  var precondition: Option[Expr] = None
  var body: Option[Expr] = None

  var funcArgs: Seq[Variable] = Seq.empty
  var localVars: Seq[Variable] = Seq.empty
  def allVariables: Seq[Variable] = funcArgs ++ localVars


  // (Translated) Constraints
  var preConstraint: Option[Expr] = None
  var bodyConstraint: Option[Expr] = None
  var postConstraint: Option[Expr] = None

  /*
    Constraints needed to prove.
    The first one is the one corresponding to the whole function.
  */
  var allConstraints: List[Constraint] = List.empty

  /*
    Generated specification.
  */
  var specConstraint: Option[Constraint] = None
  var generatedPost: Option[Expr] = None

  /*
    Simulation results.
  */
  var simulationRange: Option[Interval] = None
  var rndoff: Option[Double] = None
  var intervalRange: Option[Interval] = None
  var affineRange: Option[RationalInterval] = None

  /*
    Runtime specification.
  */
  //var runtimePre: Option[Expr] = None
  //var runtimePost: Option[Expr] = None


  /* Some stats */
  var analysisTime: Option[Long] = None
  var verificationTime:Option[Long] = None
}
