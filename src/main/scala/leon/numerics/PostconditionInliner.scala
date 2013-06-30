package leon
package numerics

import ceres.common._
import Rational.zero

import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Definitions._
import purescala.Common._

import RoundoffType._
import Utils._
import VariableShop._

class PostconditionInliner(reporter: Reporter, vcMap: Map[FunDef, VerificationCondition]) extends TransformerWithPC {
  type C = Seq[Expr]
  val initC = Nil

  var constraints = Seq[Expr]()
  var vars = Set[Variable]()
  var missingPost = false

  val postComplete = new CompleteSpecChecker

  def register(e: Expr, path: C) = path :+ e

  override def rec(e: Expr, path: C) = e match {
    case FunctionInvocation(funDef, args) =>
      val fresh = getNewFncVariable(funDef.id.name)
      vars = vars + fresh

      // The generated post is the most precise of computed and given
      vcMap(funDef).generatedPost match {
        case Some(post) =>
          assert(postComplete.check(post))
          constraints = constraints :+ replace(Map(ResultVariable() -> fresh), post)

        case None =>
          funDef.postcondition match {
            case Some(post) if (postComplete.check(post)) =>
              constraints = constraints :+ replace(Map(ResultVariable() -> fresh), post)
            case _ =>
              missingPost = true
              reporter.warning("inlining postcondition, but none found or is incomplete for " + e)
          }
      }
      fresh

    case _ =>
        super.rec(e, path)
  }

  def inlinePostcondition(pre: Expr, body: Expr, post: Expr): Option[(Expr, Expr, Expr, Set[Variable])] = {
    val (inlinedPre, cnstrPre, varsPre) = inlineFncPost(pre)
    val (inlinedPost, cnstrPost, varsPost) = inlineFncPost(post)
    val (inlinedBody, cnstrBody, varsBody) = inlineFncPost(body)
    if (missingPost) None
    else Some(And(inlinedPre, And(cnstrPre ++ cnstrBody)), inlinedBody, And(inlinedPost, And(cnstrPost)),
      varsPre ++ varsPost ++ varsBody)
  }

  //@return (expr with inlined post, contraints on fresh variables, fresh variables used)
  def inlineFncPost(expr: Expr): (Expr, Seq[Expr], Set[Variable]) = {
    constraints = Seq[Expr]()
    vars = Set[Variable]()
    val inlinedExpr = this.transform(expr)
    (inlinedExpr, constraints, vars)
  }


   // It is complete, if the result is bounded below and above and the noise is specified.
  /*private def isCompleteSpec(post: Expr): Boolean = {
    post match {
      case and @ And(args) =>
        println("args: " + args)
        val variableBounds = Utils.getVariableRecords(and)
        println("variableBounds: " + variableBounds)
        val noise = contains(and, (
          a => a match {
            case Noise(ResultVariable(), _) => true
            case _ =>
              println("other: " + a)
              false
          }))
        println("noise: " + noise)
        noise && variableBounds.contains(Variable(FreshIdentifier("#res")))

      case _ => //Need at least two conjuncts to define the noise and the range
        println("not recognized: " + post)
        false
    }
  }*/
}

// Overkill?
  class CompleteSpecChecker extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    var lwrBound = false
    var upBound = false
    var noise = false

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case LessEquals(RationalLiteral(lwrBnd), ResultVariable()) => lwrBound = true; e
      case LessThan(RationalLiteral(lwrBnd), ResultVariable()) => lwrBound = true; e
      case LessEquals(ResultVariable(), RationalLiteral(upBnd)) => upBound = true; e
      case LessThan(ResultVariable(), RationalLiteral(upBnd)) => upBound = true; e
      case Noise(ResultVariable(), RationalLiteral(value)) => noise = true; e
      case _ =>
        super.rec(e, path)
    }

    def check(e: Expr): Boolean = {
      lwrBound = false; upBound = false; noise = false
      rec(e, initC)
      lwrBound && upBound && noise
    }
  }