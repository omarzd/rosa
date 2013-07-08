package leon
package numerics

import affine._ 
import Rational.zero

import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Definitions._
import purescala.Common._

import RoundoffType._
import Utils._
import VariableShop._

class FullInliner(reporter: Reporter, vcMap: Map[FunDef, VerificationCondition]) {
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
      vars = vars ++ vc.get.localVars

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

    case Variable(_) | RationalLiteral(_) | IntLiteral(_) | UMinus(_) | Plus(_, _) | Minus(_, _) | Times(_, _) |
      Division(_, _) | Sqrt(_) => (e, emptySeq)
    case LessThan(_, _) | LessEquals(_, _) | GreaterThan(_, _) | GreaterEquals(_, _) => (e, emptySeq)    
    case Roundoff(_) | Noise(_, _) => (e, emptySeq)
    case BooleanLiteral(true) => (e, emptySeq)
    case _ =>
      reporter.error("AA cannot handle: " + e)
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