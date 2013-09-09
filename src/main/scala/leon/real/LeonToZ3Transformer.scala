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
import TreeOps._

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

    override def rec(e: Expr, path: C) = e match {
      case Roundoff(v @ Variable(_)) =>
        val delta = getNewDelta
        addExtra(constrainDelta(delta))
        Equals(variables.buddy(v), TimesR(PlusR(new RealLiteral(1), delta), v))

      case Noise(v @ Variable(_), r @ RealLiteral(value)) =>
        val freshErrorVar = getErrorVar(v)
        And(Seq(Equals(variables.buddy(v), PlusR(v, freshErrorVar)),
          LessEquals(RealLiteral(-value), freshErrorVar),
          LessEquals(freshErrorVar, r)))
      
      case Noise(res @ ResultVariable(), r @ RealLiteral(value)) =>
        val freshErrorVar = getErrorVar(res)
        And(Seq(Equals(FResVariable(), PlusR(res, freshErrorVar)),
          LessEquals(RealLiteral(-value), freshErrorVar),
          LessEquals(freshErrorVar, r)))
      case Noise(res @ FResVariable(), r @ RealLiteral(value)) =>
        val freshErrorVar = getErrorVar(res)
        And(Seq(Equals(FResVariable(), PlusR(res, freshErrorVar)),
          LessEquals(RealLiteral(-value), freshErrorVar),
          LessEquals(freshErrorVar, r)))
    
      case Noise(v @ Variable(_), expr) =>
        val freshErrorVar = getErrorVar(v)
        val value = rec(expr, path)
        And(Seq(Equals(variables.buddy(v), PlusR(v, freshErrorVar)),
          Or(
            And(LessEquals(UMinusR(value), freshErrorVar), LessEquals(freshErrorVar, value)),
            And(LessEquals(value, freshErrorVar), LessEquals(freshErrorVar, UMinusR(value)))
          )
        ))
      case Noise(res @ ResultVariable(), expr) =>
        val freshErrorVar = getErrorVar(res)
        val value = rec(expr, path)
        And(Seq(Equals(FResVariable(), PlusR(res, freshErrorVar)),
          Or(
            And(LessEquals(UMinusR(value), freshErrorVar), LessEquals(freshErrorVar, value)),
            And(LessEquals(value, freshErrorVar), LessEquals(freshErrorVar, UMinusR(value)))
          )
        ))
      case Noise(res @ FResVariable(), expr) =>
        val freshErrorVar = getErrorVar(res)
        val value = rec(expr, path)
        And(Seq(Equals(FResVariable(), PlusR(res, freshErrorVar)),
          Or(
            And(LessEquals(UMinusR(value), freshErrorVar), LessEquals(freshErrorVar, value)),
            And(LessEquals(value, freshErrorVar), LessEquals(freshErrorVar, UMinusR(value)))
          )
        ))
      
      case SqrtR(x) =>
        val r = getNewSqrtVariable
        val xR = rec(x, path)
        extraConstraints ++= Seq(Equals(TimesR(r, r), xR), LessEquals(RealLiteral(zero), r))
        r

      // floating-point arithmetic
      case UMinusF(x) => UMinusR(rec(x, path))

      case PlusF(x, y) =>
        val (mult, dlt) = getFreshRndoffMultiplier
        addExtra(constrainDelta(dlt))
        TimesR(PlusR(rec(x, path), rec(y, path)), mult)
      case MinusF(x, y) =>
        val (mult, dlt) = getFreshRndoffMultiplier
        addExtra(constrainDelta(dlt))
        TimesR(MinusR(rec(x, path), rec(y, path)), mult)
      case TimesF(x, y) =>
        val (mult, dlt) = getFreshRndoffMultiplier
        addExtra(constrainDelta(dlt))
        TimesR(TimesR(rec(x, path), rec(y, path)), mult)
      case DivisionF(x, y) =>
        val (mult, dlt) = getFreshRndoffMultiplier
        addExtra(constrainDelta(dlt))
        TimesR(DivisionR(rec(x, path), rec(y, path)), mult)
      case SqrtF(x) =>
        val n = getNewSqrtVariable
        val (mult, dlt) = getFreshRndoffMultiplier
        addExtra(constrainDelta(dlt))
        val xN = rec(x, path)
        extraConstraints ++= Seq(Equals(TimesR(n, n), xN), LessEquals(RealLiteral(zero), n))
        TimesR(n, mult)

      case r @ FloatLiteral(v, exact) =>
        if (exact) RealLiteral(v)
        else {
          val (mult, dlt) = getFreshRndoffMultiplier
          addExtra(constrainDelta(dlt))
          TimesR(RealLiteral(v), mult)
        }

      // actual
      case Actual(v @ Variable(_)) => variables.buddy(v)
      case Actual(ResultVariable()) => FResVariable()

      //within
      case WithIn(x, lwrBnd, upBnd) =>
        And(LessThan(RealLiteral(lwrBnd), x), LessThan(x, RealLiteral(upBnd))) 

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

      case FloatIfExpr(cond, thenn, elze) =>
        rec(IfExpr(cond, thenn, elze), path)

      case EqualsF(l, r) =>
        rec(Equals(l, r), path)

      case FncInvocationF(funDef, args) =>
        val newArgs = args.map(a => rec(a, path))
        newArgs.foreach(a => println("arg: " + a + "  type: " + a.getType + "   " + a.getClass))
        FunctionInvocation(funDef, args.map(a => rec(a, path)))

      case _ =>
        super.rec(e, path)
    }

    // shortcut to avoid making res variables that are never used
    // this is used for path conditions only
    def getZ3Condition(e: Expr): Expr = {
      extraConstraints = Seq[Expr]()
      val z3Expr = this.transform(e)
      And(And(extraConstraints), z3Expr)
    }

    def getZ3Expr(e: Expr, precision: Precision): Expr = {
      extraConstraints = Seq[Expr]()
      val res = Variable(FreshIdentifier("#res")).setType(RealType)
      val fres = Variable(FreshIdentifier("#fres")).setType(RealType)
      val z3Expr = replace(Map(ResultVariable() -> res, FResVariable() -> fres), this.transform(e)) 
      
      if (epsUsed) {
        println("\neps used, constraing: ")
        println(And(And(extraConstraints), z3Expr))
        And(And(extraConstraints :+ Equals(machineEps, RealLiteral(getUnitRoundoff(precision)))), z3Expr)

      }
      else
        And(And(extraConstraints), z3Expr)
    }

    // for fixedpoint arithmetic
    def getZ3ExprForFixedpoint(e: Expr): Expr = {      
      extraConstraints = Seq[Expr]()
      val noiseRemover = new NoiseRemover
      val eWoRoundoff = noiseRemover.transform(e)

      val res = Variable(FreshIdentifier("#res")).setType(RealType)
      val fres = Variable(FreshIdentifier("#fres")).setType(RealType)
      val z3Expr = replace(Map(ResultVariable() -> res, FResVariable() -> fres), this.transform(eWoRoundoff)) 
      
      assert (!epsUsed)
      And(And(extraConstraints), z3Expr)
    }    
  }