/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Common._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

import real.Trees._
import VariableShop._
import Rational._
import Precision._

class LeonToZ3Transformer(variables: VariablePool) extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    // TODO Make sure this is unique, i.e. we don't create it twice in the same constraint
    var epsUsed = false
    lazy val machineEps = { epsUsed = true; Variable(FreshIdentifier("#eps")).setType(RealType) }

    var extraConstraints = Seq[Expr]()
    def addExtra(e: Expr) = extraConstraints = extraConstraints :+ e

    var errorVars: Map[Expr, Expr] = Map.empty
    def getErrorVar(e: Expr): Expr = {
      errorVars.get(e) match {
        case Some(errorVar) => errorVar
        case None =>
          val freshErrorVar = getNewErrorVar
          errorVars = errorVars + (e -> freshErrorVar)
          freshErrorVar
      }
    }
    
    def register(e: Expr, path: C) = path :+ e

    private def constrainDelta(delta: Variable): Expr = {
      And(Seq(LessEquals(UMinus(machineEps), delta), LessEquals(delta, machineEps)))
    }

    // TODO: does not include initial roundoff
    override def rec(e: Expr, path: C) = e match {
      case Roundoff(v @ Variable(_)) =>
        val delta = getNewDelta
        addExtra(constrainDelta(delta))
        Equals(variables.buddy(v), Times(Plus(new RationalLiteral(1), delta), v))

      case Noise(v @ Variable(_), r @ RationalLiteral(value)) =>
        val freshErrorVar = getErrorVar(v)
        And(Seq(Equals(variables.buddy(v), Plus(v, freshErrorVar)),
          LessEquals(RationalLiteral(-value), freshErrorVar),
          LessEquals(freshErrorVar, r)))
      
      case Noise(res @ ResultVariable(), r @ RationalLiteral(value)) =>
        val freshErrorVar = getErrorVar(res)
        And(Seq(Equals(FResVariable(), Plus(res, freshErrorVar)),
          LessEquals(RationalLiteral(-value), freshErrorVar),
          LessEquals(freshErrorVar, r)))
      case Noise(res @ FResVariable(), r @ RationalLiteral(value)) =>
        val freshErrorVar = getErrorVar(res)
        And(Seq(Equals(FResVariable(), Plus(res, freshErrorVar)),
          LessEquals(RationalLiteral(-value), freshErrorVar),
          LessEquals(freshErrorVar, r)))
    
      case Noise(v @ Variable(_), expr) =>
        val freshErrorVar = getErrorVar(v)
        val value = rec(expr, path)
        And(Seq(Equals(variables.buddy(v), Plus(v, freshErrorVar)),
          Or(
            And(LessEquals(UMinus(value), freshErrorVar), LessEquals(freshErrorVar, value)),
            And(LessEquals(value, freshErrorVar), LessEquals(freshErrorVar, UMinus(value)))
          )
        ))
      case Noise(res @ ResultVariable(), expr) =>
        val freshErrorVar = getErrorVar(res)
        val value = rec(expr, path)
        And(Seq(Equals(FResVariable(), Plus(res, freshErrorVar)),
          Or(
            And(LessEquals(UMinus(value), freshErrorVar), LessEquals(freshErrorVar, value)),
            And(LessEquals(value, freshErrorVar), LessEquals(freshErrorVar, UMinus(value)))
          )
        ))
      case Noise(res @ FResVariable(), expr) =>
        val freshErrorVar = getErrorVar(res)
        val value = rec(expr, path)
        And(Seq(Equals(FResVariable(), Plus(res, freshErrorVar)),
          Or(
            And(LessEquals(UMinus(value), freshErrorVar), LessEquals(freshErrorVar, value)),
            And(LessEquals(value, freshErrorVar), LessEquals(freshErrorVar, UMinus(value)))
          )
        ))
      
      // translate real-valued arithmetic (makes the trees not typecheck, but we don't need to modify AbstractSolver)
      case UMinusR(t) => UMinus(rec(e, path))
      case PlusR(l, r) => Plus(rec(l, path), rec(r, path))
      case MinusR(l, r) => Minus(rec(l, path), rec(r, path))
      case TimesR(l, r) => Times(rec(l, path), rec(r, path))
      case DivisionR(l, r) => Division(rec(l, path), rec(r, path))
      case SqrtR(x) =>
        val r = getNewSqrtVariable
        val xR = rec(x, path)
        extraConstraints ++= Seq(Equals(Times(r, r), xR), LessEquals(RationalLiteral(zero), r))
        r

      // floating-point arithmetic
      case UMinusF(x) => UMinus(rec(x, path))

      case PlusF(x, y) =>
        val (mult, dlt) = getFreshRndoffMultiplier
        addExtra(constrainDelta(dlt))
        Times(Plus(rec(x, path), rec(y, path)), mult)
      case MinusF(x, y) =>
        val (mult, dlt) = getFreshRndoffMultiplier
        addExtra(constrainDelta(dlt))
        Times(Minus(rec(x, path), rec(y, path)), mult)
      case TimesF(x, y) =>
        val (mult, dlt) = getFreshRndoffMultiplier
        addExtra(constrainDelta(dlt))
        Times(Times(rec(x, path), rec(y, path)), mult)
      case DivisionF(x, y) =>
        val (mult, dlt) = getFreshRndoffMultiplier
        addExtra(constrainDelta(dlt))
        Times(Division(rec(x, path), rec(y, path)), mult)
      case SqrtF(x) =>
        val n = getNewSqrtVariable
        val (mult, dlt) = getFreshRndoffMultiplier
        addExtra(constrainDelta(dlt))
        val xN = rec(x, path)
        extraConstraints ++= Seq(Equals(Times(n, n), xN), LessEquals(RationalLiteral(zero), n))
        Times(n, mult)

      case r @ RationalLiteral(v) =>
        if (r.exact) r
        else {
          // TODO: we don't want to do this for the ideal part!
          val (mult, dlt) = getFreshRndoffMultiplier
          addExtra(constrainDelta(dlt))
          Times(r, mult)
        }

      // actual
      case Actual(v @ Variable(_)) => variables.buddy(v)
      case Actual(ResultVariable()) => FResVariable()

      //within
      case WithIn(v @ Variable(_), lwrBnd, upBnd) =>
        And(LessThan(RationalLiteral(lwrBnd), v), LessThan(v, RationalLiteral(upBnd))) 

      case FncValue(s) =>
        val fresh = getNewXFloatVar
        val spec = replace(Map(ResultVariable() -> fresh), s)
        addExtra(rec(spec, path))
        fresh

      case FncBody(name, body) =>
        val fresh = getNewFncVariable(name)
        addExtra(Equals(fresh, rec(body, path)))
        fresh

      // normally this is approximated
      case FncBodyF(name, body) =>
        val fresh = getNewFncVariable(name + "_f")
        addExtra(Equals(fresh, rec(body, path)))
        fresh

      case _ =>
        super.rec(e, path)
    }

    def getZ3Expr(e: Expr, precision: Precision): Expr = {
      extraConstraints = Seq[Expr]()
      val res = Variable(FreshIdentifier("#res")).setType(RealType)
      val fres = Variable(FreshIdentifier("#fres")).setType(RealType)
      val z3Expr = replace(Map(ResultVariable() -> res, FResVariable() -> fres), this.transform(e)) 
      
      if (epsUsed)
        And(And(extraConstraints :+ Equals(machineEps, RationalLiteral(getUnitRoundoff(precision)))), z3Expr)
      else
        And(And(extraConstraints), z3Expr)
    }
  }