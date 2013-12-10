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

class LeonToZ3Transformer(variables: VariablePool, precision: Precision) extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    // TODO Make sure this is unique, i.e. we don't create it twice in the same constraint
    var epsUsed = false
    var epsVariable: Variable = Variable(FreshIdentifier("#eps")).setType(RealType)
    def machineEps = { epsUsed = true; epsVariable }

    def initEps = {
      epsUsed = false
      epsVariable = Variable(FreshIdentifier("#eps")).setType(RealType)
    }

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

    private def constrainDelta(delta: Variable): Expr = And(Seq(LessEquals(UMinusR(machineEps), delta), LessEquals(delta, machineEps)))

    override def rec(e: Expr, path: C) = e match {
      case Roundoff(v @ Variable(_)) =>
        val delta = getNewDelta
        addExtra(constrainDelta(delta))
        Equals(variables.buddy(v), TimesR(PlusR(new RealLiteral(1), delta), v))

      // For bspline 3 to work, we need this:
      // TODO: test if this is better in general?
      /*case Noise(v @ Variable(_), r @ RealLiteral(value)) =>
        And(LessEquals(RealLiteral(-value), MinusR(v, variables.buddy(v))), 
            LessEquals(MinusR(v, variables.buddy(v)), r))
      case Noise(res @ ResultVariable(), r @ RealLiteral(value)) =>
        And(LessEquals(RealLiteral(-value), MinusR(res, FResVariable())),
            LessEquals(MinusR(res, FResVariable()), r))
      case Noise(res @ FResVariable(), r @ RealLiteral(value)) =>
        throw new Exception("???")
        null
        And(LessEquals(RealLiteral(-value), MinusR(ress, buddy(ress))),
            LessEquals(MinusR(ress, buddy(ress)), r))
      */


      case Noise(v @ Variable(_), r @ RealLiteral(value)) =>
        val freshErrorVar = getErrorVar(v)
        And(Seq(Equals(variables.buddy(v), PlusR(v, freshErrorVar)),
          LessEquals(RealLiteral(-value), freshErrorVar),
          LessEquals(freshErrorVar, r)))
      
        /*val freshErrorVar = getErrorVar(res)
          And(Seq(Equals(FResVariable(), PlusR(res, freshErrorVar)),
          LessEquals(RealLiteral(-value), freshErrorVar),
          LessEquals(freshErrorVar, r)))
        */

      case Noise(v @ Variable(_), expr) =>
        val freshErrorVar = getErrorVar(v)
        val value = rec(expr, path)
        And(Seq(Equals(variables.buddy(v), PlusR(v, freshErrorVar)),
          Or(
            And(LessEquals(UMinusR(value), freshErrorVar), LessEquals(freshErrorVar, value)),
            And(LessEquals(value, freshErrorVar), LessEquals(freshErrorVar, UMinusR(value)))
          )
        ))
      
        /*val freshErrorVar = getErrorVar(res)
          val value = rec(expr, path)
          And(Seq(Equals(FResVariable(), PlusR(res, freshErrorVar)),
          Or(
            And(LessEquals(UMinusR(value), freshErrorVar), LessEquals(freshErrorVar, value)),
            And(LessEquals(value, freshErrorVar), LessEquals(freshErrorVar, UMinusR(value)))
          )
        ))*/
  
      case RelError(v @ Variable(_), r @  RealLiteral(value)) =>
        val freshErrorVar = getErrorVar(v)
        And(Seq(Equals(variables.buddy(v), PlusR(v, freshErrorVar)),
          Or(
            And(LessEquals(UMinusR(TimesR(r, v)), freshErrorVar),LessEquals(freshErrorVar, TimesR(r, v))),
            And(LessEquals(TimesR(r, v), freshErrorVar),LessEquals(freshErrorVar, UMinusR(TimesR(r, v))))
          )
        ))
      
      case InitialNoise(v @ Variable(_)) => getErrorVar(v)
      
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
      
      //within
      case WithIn(x, lwrBnd, upBnd) =>
        And(LessThan(RealLiteral(lwrBnd), x), LessThan(x, RealLiteral(upBnd))) 

      case FncValue(spec, specExpr) =>
        val fresh = getNewXFloatVar
        addExtra(rec(replace(Map(Variable(spec.id) -> fresh), specExpr), path))
        fresh

      case FncBody(name, body) =>
        val fresh = getNewFncVariable(name)
        rec(body, path) match {
          case And(args) => 
            addExtra(And(args.init :+ Equals(fresh, args.last)))
          case x =>
            addExtra(Equals(fresh, x))
        }
        fresh
        

      // normally this is approximated
      case FncBodyF(name, body) =>
        val fresh = getNewFncVariable(name + "_f")
        rec(body, path) match {
          case And(args) => 
            addExtra(And(args.init :+ Equals(fresh, args.last)))
          case x =>
            addExtra(Equals(fresh, x))
        }
        fresh

      case FloatIfExpr(cond, thenn, elze) =>
        rec(IfExpr(cond, thenn, elze), path)

      case EqualsF(l, r) =>
        rec(Equals(l, r), path)

      case FncInvocationF(funDef, args) =>
        val newArgs = args.map(a => rec(a, path))
        newArgs.foreach(a => println("arg: " + a + "  type: " + a.getType + "   " + a.getClass))
        FunctionInvocation(funDef, args.map(a => rec(a, path)))

      case Times(_, _) | Plus(_, _) | Division(_, _) | Minus(_, _) | UMinus(_) =>
        throw new Exception("found integer arithmetic in LeonToZ3Transformer")
        null

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

    def getZ3Expr(e: Expr): Expr = {
      extraConstraints = Seq[Expr]()
      initEps
      //val res = Variable(FreshIdentifier("#res")).setType(RealType)
      //val fres = Variable(FreshIdentifier("#fres")).setType(RealType)

      precision match {
        case FPPrecision(bts) =>
          // Only remove roundoffs from the precondition, since our translation (for now) cannot handle it,
          // and we don't need them since we use the approximation anyway
          val roundoffRemover = new RoundoffRemover
          val eWoRoundoff = roundoffRemover.transform(e)
          //val z3Expr = replace(Map(ResultVariable() -> res, FResVariable() -> fres), this.transform(eWoRoundoff)) 
          val z3Expr = this.transform(eWoRoundoff)
          assert (!epsUsed)
          And(And(extraConstraints), z3Expr)

        case _ =>
          ///val z3Expr = replace(Map(ResultVariable() -> res, FResVariable() -> fres), this.transform(e)) 
          val z3Expr = this.transform(e)
          if (epsUsed) And(And(extraConstraints :+ Equals(machineEps, RealLiteral(getUnitRoundoff(precision)))), z3Expr)
          else And(And(extraConstraints), z3Expr)          
      }
    } 
  }