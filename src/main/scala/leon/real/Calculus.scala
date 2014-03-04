/* Copyright 2013-2014 EPFL, Lausanne */

package leon
package real

import purescala.Trees.{Expr, Variable, And, LessEquals, Equals, IntLiteral}
import purescala.Common.Identifier
import Trees._
import TreeOps.collectPowers
import Rational._

object Calculus {

  implicit class SmartExpr(e: Expr) {
    def unary_-(): Expr = UMinusR(e)

    def +(other: Expr): Expr = PlusR(e, other)
    def -(other: Expr): Expr = MinusR(e, other)
    def *(other: Expr): Expr = TimesR(e, other)
    def /(other: Expr): Expr = DivisionR(e, other)

    def *(dbl: Double): Expr = TimesR(e, RealLiteral(Rational(dbl)))
    def +(dbl: Double): Expr = PlusR(e, RealLiteral(Rational(dbl)))

    def &&(other: Expr): Expr = And(e, other)

    def <=(other: Expr): Expr = LessEquals(e, other)
    def <=(dbl: Double): Expr = LessEquals(e, RealLiteral(Rational(dbl)))
    def ===(other: Expr): Expr = Equals(e, other)
  }

  implicit class SmartDouble(dbl: Double) {
    def <=(e: Expr): Expr = LessEquals(RealLiteral(Rational(dbl)), e)
  }

  //implicit def doubleToExpr(dbl: Double): Expr = RealLiteral(Rational(dbl))

  def r_(dbl: Double): Expr = RealLiteral(Rational(dbl))

  // we can probably also use the partial unicode sign
  // TODO: some of the cleanups shouldn't be needed no?
  // since cleanUp is called just before d returns...
  def d(expr: Expr, wrt: Identifier): Expr = {
    val expr2 = collectPowers(expr)
    val newExpr: Expr = expr2 match {
      case TimesR(c @ RealLiteral(r), x) => c * d(x, wrt)
      case TimesR(x, c @ RealLiteral(r)) => c * d(x, wrt)

      // variable treated as constant
      case TimesR(p @ Variable(id), x) if (id != wrt) => p * d(x, wrt)
      case TimesR(x, p @ Variable(id)) if (id != wrt) => p * d(x, wrt)
      
      case Variable(id) if(id == wrt) => RealLiteral(one)
      case v: Variable => RealLiteral(zero)
      case c: RealLiteral => RealLiteral(zero)
      
      case UMinusR(x) => UMinusR(cleanUp(d(x,wrt)))
      case PlusR(l, r) => d(l, wrt) + d(r, wrt)
      case MinusR(l, r) => d(l, wrt) - d(r, wrt)
      case TimesR(l, r) => cleanUp(d(l,wrt) * r) + cleanUp(l * d(r,wrt))

      case DivisionR(f, c @ RealLiteral(r)) => DivisionR(cleanUp(d(f,wrt)), c)

      case DivisionR(f, g) =>
        cleanUp(cleanUp(d(f,wrt) * g) - cleanUp(d(g,wrt) * f)) / (g*g)
      
      case SqrtR(e) => d(e,wrt) / (RealLiteral(Rational(2.0)) * SqrtR(e))
      case PowerR(base, c @ IntLiteral(i)) =>
        RealLiteral(Rational(i)) * 
          cleanUp(d(base,wrt) * cleanUp(PowerR(base, IntLiteral(i - 1))))
      //case PowerR(base, v @ Variable(id)) if (id != wrt) =>
      //  v * cleanUp(d(base,wrt) * cleanUp(PowerR(base, MinusR(v, RealLiteral(one)))))
    }
    //println("\nd("+pretty(e)+") --> " + pretty(newExpr))
    val tmp = cleanUp(newExpr)
    //println("clean up: " + pretty(tmp))
    tmp
  }
  
  def cleanUp(e: Expr): Expr = e match {
    // Clean up zeroes
    case PlusR(RealLiteral(r), x) if (r == zero) => x
    case PlusR(x, RealLiteral(r)) if (r == zero) => x
    case MinusR(x, RealLiteral(r)) if (r == zero) => x
    case MinusR(RealLiteral(r), x) if (r == zero) => UMinusR(x)
    case TimesR(RealLiteral(r), x) if (r == zero) => RealLiteral(zero)
    case TimesR(x, RealLiteral(r)) if (r == zero) => RealLiteral(zero)
    case DivisionR(RealLiteral(r), x) if (r == zero) => RealLiteral(zero)

    // Clean up trivial expressions
    case TimesR(RealLiteral(r), x) if (r == one) => x
    case TimesR(x, RealLiteral(r)) if (r == one) => x
    case UMinusR(RealLiteral(r)) => RealLiteral(-r)
    case UMinusR(UMinusR(x)) => x
    case PowerR(b, RealLiteral(r)) if (r == one) => b
    case PowerR(b, IntLiteral(i)) if (i == 1) => b
    case TimesR(UMinusR(x), UMinusR(y)) => TimesR(x, y)
    case UMinusR(TimesR(x, UMinusR(y))) => TimesR(x, y)
    case UMinusR(TimesR(UMinusR(x), y)) => TimesR(x, y)

    // Fixme: this is probably not great if we don't have integers
    case PlusR(RealLiteral(r1), RealLiteral(r2)) => RealLiteral(r1 + r2)
    case TimesR(RealLiteral(r1), RealLiteral(r2)) => RealLiteral(r1 * r2)
    case TimesR(RealLiteral(r1), TimesR(RealLiteral(r2), x)) =>
      TimesR(RealLiteral(r1 * r2), x)
    case TimesR(RealLiteral(r1), DivisionR(RealLiteral(r2), x)) =>
      DivisionR(RealLiteral(r1 * r2), x)
    case _ => e
  }

}