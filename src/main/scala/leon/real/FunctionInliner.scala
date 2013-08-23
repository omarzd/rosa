/* Copyright 2013 EPFL, Lausanne */

package leon
package real


import Rational.zero

import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Definitions._
import purescala.Common._

import real.Trees._
//import Utils._
import VariableShop._

class PostconditionInliner(reporter: Reporter, vcMap: Map[FunDef, VerificationCondition]) extends TransformerWithPC {
  type C = Seq[Expr]
  val initC = Nil

  var constraints = Seq[Expr]()
  var vars = Set[Variable]()
  var missingPost = false

  //val postComplete = new CompleteSpecChecker

  def register(e: Expr, path: C) = path :+ e

  override def rec(e: Expr, path: C) = e match {
    case FunctionInvocation(funDef, args) =>
      val arguments: Map[Expr, Expr] = funDef.args.map(decl => decl.toVariable).zip(args).toMap
      
      // TODO
      /*val firstChoice = funDef.postcondition
      val secondChoice = vcMap(funDef).spec
      val post = firstChoice match {
        case Some(post) if (postComplete.check(post)) => Some(post)
        case _ => secondChoice match {
          case Some(post) if (postComplete.check(post)) => Some(post)
          case _ => None
        }
      }*/
      val post = funDef.postcondition.get
      FncValue(replace(arguments, post))
    case _ =>
        super.rec(e, path)
  }

  /*def inlinePostcondition(pre: Expr, body: Expr, post: Expr): Option[(Expr, Expr, Expr, Set[Variable])] = {
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
  }*/
}

// Overkill?
  /*class CompleteSpecChecker extends TransformerWithPC {
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
      case Noise(ResultVariable(), _) => noise = true; e
      case _ =>
        super.rec(e, path)
    }

    def check(e: Expr): Boolean = {
      lwrBound = false; upBound = false; noise = false
      rec(e, initC)
      lwrBound && upBound && noise
    }
  }*/

class FunctionInliner(reporter: Reporter, vcMap: Map[FunDef, VerificationCondition]) {
  val emptySeq = Seq[Expr]()

  var constraints = Seq[Expr]()
  var vars = Set[Variable]()

  def rec(e: Expr): (Expr, Seq[Expr]) = e match {
    case Equals(l, r) =>
      val (rhs, rhsCnstr) = rec(r)
      if (rhsCnstr.isEmpty)
        (Equals(l, r), emptySeq)
      else
        (And(rhsCnstr :+ Equals(l, rhs)), emptySeq)

    case FunctionInvocation(funDef, args) =>
      val fresh = getNewFncVariable(funDef.id.name)
      vars = vars + fresh

      val vc = vcMap.get(funDef)
      if(vc.isEmpty) {throw new Exception("Trying to inline missing function: " + funDef.id.toString)}
      val fncBody = vc.get.body
      //vars = vars ++ vc.get.localVars

      val arguments: Map[Expr, Expr] = funDef.args.map(decl => decl.toVariable).zip(args).toMap
      val (bodyCnstr, cnstrs) = rec(replace(arguments + (ResultVariable() -> fresh), fncBody))
      (fresh, cnstrs :+ bodyCnstr)

    case And(args) =>
      var cnstrs = emptySeq
      var newArgs = emptySeq
      for (arg <- args) {
        val (expr, cns) = rec(arg)
        cnstrs ++= cns
        newArgs :+= expr
      }
      (And(newArgs), cnstrs)

    case IfExpr(cond, then, elze) =>
      val (newCond, condCnsts) = rec(cond)
      val (newThen, thenCnsts) = rec(then)
      val (newElze, elzeCnsts) = rec(elze)
      (IfExpr(newCond, newThen, newElze), condCnsts ++ thenCnsts ++ elzeCnsts)

    case Variable(_) | RationalLiteral(_) => (e, emptySeq)

    case UMinusR(expr) =>
      val (exprIn, constr) = rec(expr)
      (UMinusR(exprIn), constr)

    case SqrtR(expr) =>
      val (exprIn, constr) = rec(expr)
      (SqrtR(exprIn), constr)

    case PlusR(lhs, rhs) =>
      val (lhsIn, lhsCns) = rec(lhs)
      val (rhsIn, rhsCns) = rec(rhs)
      (PlusR(lhsIn, rhsIn), lhsCns ++ rhsCns)

    case MinusR(lhs, rhs) =>
      val (lhsIn, lhsCns) = rec(lhs)
      val (rhsIn, rhsCns) = rec(rhs)
      (MinusR(lhsIn, rhsIn), lhsCns ++ rhsCns)

    case TimesR(lhs, rhs) =>
      val (lhsIn, lhsCns) = rec(lhs)
      val (rhsIn, rhsCns) = rec(rhs)
      (TimesR(lhsIn, rhsIn), lhsCns ++ rhsCns)

    case DivisionR(lhs, rhs) =>
      val (lhsIn, lhsCns) = rec(lhs)
      val (rhsIn, rhsCns) = rec(rhs)
      (DivisionR(lhsIn, rhsIn), lhsCns ++ rhsCns)

    case LessThan(_, _) | LessEquals(_, _) | GreaterThan(_, _) | GreaterEquals(_, _) => (e, emptySeq)    
    case Noise(_, _) => (e, emptySeq)
    case BooleanLiteral(true) => (e, emptySeq)
    case _ =>
      reporter.error("function inlining cannot handle: " + e)
      (e, emptySeq)
  }

  def inlineFunctions(pre: Expr, body: Expr, post: Expr): (Expr, Expr, Expr, Set[Variable]) = {
    vars = Set[Variable]()
    val (newPre, cnstrPre) = rec(pre)
    val (newBody, cnstrBody) = rec(body)
    val (newPost, cnstrPost) = rec(post)
    
    (And(And(cnstrPre), newPre), And(And(cnstrBody), And(newBody, And(cnstrPost))), newPost, vars)
  }

}