/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._


import xlang.Trees._
import real.Trees._

object TreeOps {
  
  // can return several, as we may have an if-statement
  def getInvariantCondition(expr: Expr): List[Expr] = expr match {
    case IfExpr(cond, thenn, elze) => getInvariantCondition(thenn) ++ getInvariantCondition(elze)
    case Let(binder, value, body) => getInvariantCondition(body)
    case LessEquals(_, _) | LessThan(_, _) | GreaterThan(_, _) | GreaterEquals(_, _) => List(expr)
    case Equals(_, _) => List(expr)
    case _ =>
      println("!!! Expected invariant, but found: " + expr.getClass)
      List(BooleanLiteral(false))
  }

  // Has to run before we removed the lets!
  // Basically the first free expression that is not an if or a let is the result
  def addResult(expr: Expr): Expr = expr match {
    case ifThen @ IfExpr(_, _, _) => Equals(ResultVariable(), ifThen)
    case Let(binder, value, body) => Let(binder, value, addResult(body))
    case UMinusR(_) | PlusR(_, _) | MinusR(_, _) | TimesR(_, _) | DivisionR(_, _) | SqrtR(_) | FunctionInvocation(_, _) | Variable(_) =>
      Equals(ResultVariable(), expr)
    case Block(exprs, last) => Block(exprs, addResult(last))
    case _ => expr
  }

  def convertLetsToEquals(expr: Expr): Expr = expr match {
    case Equals(l, r) => Equals(l, convertLetsToEquals(r))
    case IfExpr(cond, thenn, elze) =>
      IfExpr(cond, convertLetsToEquals(thenn), convertLetsToEquals(elze))

    case Let(binder, value, body) =>
      And(Equals(Variable(binder), convertLetsToEquals(value)), convertLetsToEquals(body))

    case Block(exprs, last) =>
      And(exprs.map(e => convertLetsToEquals(e)) :+ convertLetsToEquals(last))

    case _ => expr

  }
}