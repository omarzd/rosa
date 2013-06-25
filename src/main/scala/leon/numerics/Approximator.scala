package leon
package numerics

import ceres.common.{Rational, RationalInterval}

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

import affine.{XFloat, XFloatConfig}
import affine.XFloat._

import Utils._

import Valid._
import ApproximationType._
import Precision._

case class APath(idealCondition: Expr, noisyCondition: Expr, ideal: Expr, noisy: Expr)
case class Approximation(pre: Expr, paths: Set[APath], globalBody: Expr, post: Expr)

// skipz3Only: skip the first approximation where we feed Z3 the full initial constraint
class Approximator(reporter: Reporter, c: Constraint, parameters: Seq[Variable], unitRoundoff: Rational, skipZ3Only: Boolean = false) {


  // determine the strategy up-front
  var approxStrategy =
    if (containsFunctionCalls(c.body) || containsFunctionCalls(c.pre) || containsFunctionCalls(c.post)) {
      if(skipZ3Only) Seq(PostInlining_None, PostInlining_AA, FullInlining_None, FullInlining_AA)
      else Seq(Uninterpreted_None, PostInlining_None, PostInlining_AA, FullInlining_None, FullInlining_AA)
    } else {
      if (skipZ3Only) Seq(NoFncs_AA)
      else Seq(Uninterpreted_None, NoFncs_AA)
    }

  val (resVar, eps, buddies) = getInitialVariables(parameters)
  val trans = new NumericConstraintTransformer(buddies, resVar, eps, RoundoffType.RoundoffMultiplier, reporter)


  val initialPrecondition = trans.transformCondition(c.pre)
  val initialPostcondition = trans.transformCondition(c.post)

  val resultError = Equals(getNewResErrorVariable, Minus(resVar, buddies(resVar)))
  val machineEpsilon = Equals(eps, RationalLiteral(unitRoundoff))
  val toAddEverywhere = And(resultError, machineEpsilon)

  def nextApproximation: Option[Approximation] = {
    reporter.info("Next approximation: " + approxStrategy.head)
    val newApprox = approxStrategy.head match {
      case Uninterpreted_None =>
        //only one path: whole body
        val (r, n) = trans.transformBlock(c.body)
        
        Some(Approximation(initialPrecondition, Set(APath(True, True, r, n)), toAddEverywhere, initialPostcondition))
      case _ => None

    
    }
    //println("newApprox: " + newApprox)
    approxStrategy = approxStrategy.tail
    newApprox
  }


}