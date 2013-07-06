package leon
package numerics

import ceres.common.Interval
import ceres.smartfloat._

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import Valid._
import Utils._

import affine._

// It's one for each method, but may store several conditions to be proven.
// The first constraint is the one corresponding to the whole function.
case class VerificationCondition(funDef: FunDef, inputs: Map[Variable, Record], precondition: Expr, body: Expr,
  allFncCalls: Set[String], allConstraints: List[Constraint], specConstraint: Option[Constraint]) {

  val id = funDef.id.toString
  val fncArgs: Seq[Variable] = funDef.args.map(v => Variable(v.id).setType(RealType))
  val localVars: Seq[Variable] = allLetDefinitions(funDef.body.get).map(letDef => Variable(letDef._1).setType(RealType))
  val allVariables: Seq[Variable] = fncArgs ++ localVars

  def proven: Boolean =
    // Only generate spec for all
    if (allConstraints.isEmpty) !generatedPost.isEmpty
    else allConstraints.forall(c => !c.status.isEmpty && c.status.get == VALID)

  /* Generated specification. */
  var generatedPost: Option[Expr] = None
  val isInvariant = funDef.returnType == BooleanType
  
  /* Simulation results. */
  var simulationRange: Option[Interval] = None
  var rndoff: Option[Double] = None
  var intervalRange: Option[RationalInterval] = None
  var affineRange: Option[RationalInterval] = None

  /* Some stats */
  var analysisTime: Option[Long] = None
  var verificationTime:Option[Long] = None

  override def toString: String = "vc(" + id+")"
}
