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

class NumericConstraintTransformer(buddy: Map[Expr, Expr], ress: Variable, eps: Variable,
  roundoffType: RoundoffType, reporter: Reporter) {

    var errors: Seq[String] = Seq.empty
    var extraConstraints: Seq[Expr] = Seq.empty

    def addExtra(e: Expr) = extraConstraints = extraConstraints :+ e

    def init = {
      errors = Seq.empty
      extraConstraints = Seq(Equals(eps, RationalLiteral(unitRndoff)))
    }

    def printErrors = for (err <- errors) reporter.error(err)


    def transformBlock(body: Expr): (Expr, Expr) = {
      init
      val (bodyCReal, bodyCNoisy) = transformBody(body)
      printErrors
      (bodyCReal, And(Seq(bodyCNoisy) ++ extraConstraints))
    }

    def transformCondition(cond: Expr): Expr = {
      init
      val condC = cond match {
        case And(args) => args.map(p => transformPrePost(p))
        case _ => Seq(transformPrePost(cond))
      }
      printErrors
      And(condC ++ extraConstraints)
    }

    def getNoisyCondition(e: Expr): Expr = {
      replace(buddy, e)
    }


    def transformPrePost(e: Expr): Expr = e match {
      case Noise(v @ Variable(id), r @ RationalLiteral(value)) =>
        if (value < Rational.zero) { errors = errors :+ "Noise must be positive."; Error("negative noise " + value).setType(BooleanType)
        } else {
          And(LessEquals(RationalLiteral(-value), Minus(v, buddy(v))),
            LessEquals(Minus(v, buddy(v)), r))
        }

      case Noise(ResultVariable(), r @ RationalLiteral(value)) =>
        if (value < Rational.zero) { errors = errors :+ "Noise must be positive."; Error("negative noise " + value).setType(BooleanType)
        } else {
          And(LessEquals(RationalLiteral(-value), Minus(ress, buddy(ress))),
            LessEquals(Minus(ress, buddy(ress)), r))
        }

      case Roundoff(v @ Variable(id)) =>
        val delta = getNewDelta
        extraConstraints = extraConstraints :+ constrainDelta(delta)
        Equals(buddy(v), Times(Plus(new RationalLiteral(1), delta), v))

      case LessThan(ResultVariable(), RationalLiteral(_)) | LessThan(RationalLiteral(_), ResultVariable()) =>
        replace(Map(ResultVariable() -> ress), e)
      case LessEquals(ResultVariable(), RationalLiteral(_)) | LessEquals(RationalLiteral(_), ResultVariable()) =>
        replace(Map(ResultVariable() -> ress), e)
      case GreaterThan(ResultVariable(), RationalLiteral(_)) | GreaterThan(RationalLiteral(_), ResultVariable()) =>
        replace(Map(ResultVariable() -> ress), e)
      case GreaterEquals(ResultVariable(), RationalLiteral(_)) | GreaterEquals(RationalLiteral(_), ResultVariable()) =>
        replace(Map(ResultVariable() -> ress), e)

      case _ => e
    }



  def transformBody(e: Expr): (Expr, Expr) = e match {

    case Equals(v @ Variable(id), valueExpr) =>
      val (real, noisy) = transformBody(valueExpr)
      (Equals(v, real), Equals(buddy(v), noisy))

    case Equals(ResultVariable(), valueExpr) =>
      val (real, noisy) = transformBody(valueExpr)
      (Equals(ress, real), Equals(buddy(ress), noisy))

    case IfExpr(cond, then, elze) =>
      val (thenR, thenN) = transformBody(then)
      val (elseR, elseN) = transformBody(elze)
      val (realC, noisyC) = transformBody(cond)
      (IfExpr(realC, thenR, elseR), IfExpr(noisyC, thenN, elseN))

    case And(args) =>
      var esReal: Seq[Expr] = Seq.empty
      var esNoisy: Seq[Expr] = Seq.empty

      for (arg <- args) {
        val (eReal, eNoisy) = transformBody(arg)
        esReal = esReal :+ eReal
        esNoisy = esNoisy :+ eNoisy
      }
      (And(esReal), And(esNoisy))

    case Plus(x, y) =>
      val (mult, dlt) = getFreshRndoffMultiplier
      addExtra(constrainDelta(dlt))
      val (xR, xN) = transformBody(x)
      val (yR, yN) = transformBody(y)
      (Plus(xR, yR), Times(Plus(xN, yN), mult))

    case Minus(x, y) =>
      val (mult, dlt) = getFreshRndoffMultiplier
      addExtra(constrainDelta(dlt))
      val (xR, xN) = transformBody(x)
      val (yR, yN) = transformBody(y)
      (Minus(xR, yR), Times(Minus(xN, yN), mult))

    case Times(x, y) =>
      val (mult, dlt) = getFreshRndoffMultiplier
      addExtra(constrainDelta(dlt))
      val (xR, xN) = transformBody(x)
      val (yR, yN) = transformBody(y)
      (Times(xR, yR), Times(Times(xN, yN), mult))

    case Division(x, y) =>
      val (mult, dlt) = getFreshRndoffMultiplier
      addExtra(constrainDelta(dlt))
      val (xR, xN) = transformBody(x)
      val (yR, yN) = transformBody(y)
      (Division(xR, yR), Times(Division(xN, yN), mult))

    case UMinus(x) =>
      val (xR, xN) = transformBody(x)
      (UMinus(xR), UMinus(xN))

    case Sqrt(x) =>
      val (r, n) = getNewSqrtVariable
      val (mult, dlt) = getFreshRndoffMultiplier
      addExtra(constrainDelta(dlt))
      val (xR, xN) = transformBody(x)
      extraConstraints = extraConstraints ++ Seq(Equals(Times(r, r), xR), LessEquals(RationalLiteral(zero), r))
      extraConstraints = extraConstraints ++ Seq(Equals(Times(n, n), xN), LessEquals(RationalLiteral(zero), n))
      (r, Times(n, mult))

    case LessEquals(x, y) =>
      val (xR, xN) = transformBody(x)
      val (yR, yN) = transformBody(y)
      (LessEquals(xR, yR), LessEquals(xN, yN))

    case LessThan(x, y) =>
      val (xR, xN) = transformBody(x)
      val (yR, yN) = transformBody(y)
      (LessThan(xR, yR), LessThan(xN, yN))

    case GreaterEquals(x, y) =>
      val (xR, xN) = transformBody(x)
      val (yR, yN) = transformBody(y)
      (GreaterEquals(xR, yR), GreaterEquals(xN, yN))

    case GreaterThan(x, y) =>
      val (xR, xN) = transformBody(x)
      val (yR, yN) = transformBody(y)
      (GreaterThan(xR, yR), GreaterThan(xN, yN))

    case v: Variable => (v, buddy(v))

    case r: RationalLiteral =>
      // TODO: roundoff only if not exact
      val (mult, dlt) = getFreshRndoffMultiplier
      addExtra(constrainDelta(dlt))
      (r, Times(r, mult))

    case fnc @ FunctionInvocation(funDef, args) =>
      (fnc, FunctionInvocation(funDef, args.map(a => buddy(a))))

    case BooleanLiteral(true) => (BooleanLiteral(true), BooleanLiteral(true))
    case _ =>
      errors = errors :+ ("Unknown body! " + e);
      (Error("unknown body: " + e).setType(BooleanType), Error("unknown body: " + e).setType(BooleanType))
  }

  private def constrainDelta(delta: Variable): Expr = {
    And(Seq(LessEquals(UMinus(eps), delta),
            LessEquals(delta, eps)))
  }

   // @return (constraint, deltas) (the expression with added roundoff, the deltas used)
  /*private def addRndoff(expr: Expr): (Expr, List[Variable]) = expr match {
    case Plus(x, y) =>
      val (xExpr, xDeltas) = addRndoff(x)
      val (yExpr, yDeltas) = addRndoff(y)
      val u = Plus(xExpr, yExpr)
      val (rndoff, delta) = getRndoff(u)

      (Plus(u, rndoff), xDeltas ++ yDeltas ++ List(delta))

    case Minus(x, y) =>
      val (xExpr, xDeltas) = addRndoff(x)
      val (yExpr, yDeltas) = addRndoff(y)
      val u = Minus(xExpr, yExpr)
      val (rndoff, delta) = getRndoff(u)
      (Plus(u, rndoff), xDeltas ++ yDeltas ++ List(delta))

    case Times(x, y) =>
      val (xExpr, xDeltas) = addRndoff(x)
      val (yExpr, yDeltas) = addRndoff(y)
      val u = Times(xExpr, yExpr)
      val (rndoff, delta) = getRndoff(u)
      (Plus(u, rndoff), xDeltas ++ yDeltas ++ List(delta))

    case Division(x, y) =>
      val (xExpr, xDeltas) = addRndoff(x)
      val (yExpr, yDeltas) = addRndoff(y)
      val u = Division(xExpr, yExpr)
      val (rndoff, delta) = getRndoff(u)
      (Plus(u, rndoff), xDeltas ++ yDeltas ++ List(delta))

    case UMinus(x) =>
      val (xExpr, xDeltas) = addRndoff(x)
      (UMinus(xExpr), xDeltas)

    case LessEquals(x, y) =>
      val (xExpr, xDeltas) = addRndoff(x)
      val (yExpr, yDeltas) = addRndoff(y)
      (LessEquals(xExpr, yExpr), xDeltas ++ yDeltas)

    case LessThan(x, y) =>
      val (xExpr, xDeltas) = addRndoff(x)
      val (yExpr, yDeltas) = addRndoff(y)
      (LessEquals(xExpr, yExpr), xDeltas ++ yDeltas)

    case GreaterEquals(x, y) =>
      val (xExpr, xDeltas) = addRndoff(x)
      val (yExpr, yDeltas) = addRndoff(y)
      (LessEquals(xExpr, yExpr), xDeltas ++ yDeltas)

    case GreaterThan(x, y) =>
      val (xExpr, xDeltas) = addRndoff(x)
      val (yExpr, yDeltas) = addRndoff(y)
      (LessEquals(xExpr, yExpr), xDeltas ++ yDeltas)

    case v: Variable => (v, List())

    case r: RationalLiteral => (r, List())

    case fnc: FunctionInvocation => (fnc, List())
    case _=>
      println("Cannot add roundoff to: " + expr)
      (Error(""), List())

  }*/

    /*def transformBody(e: Expr): Expr = e match {

      case Equals(v @ Variable(id), valueExpr) =>
        val noisy = transformBody(valueExpr)
        Equals(buddy(v), noisy)

      case Equals(ResultVariable(), valueExpr) =>
        val noisy = transformBody(valueExpr)
        Equals(buddy(ress), noisy)


      case IfExpr(cond, then, elze) =>
        val thenNoisy = transformBody(then)
        val elseNoisy = transformBody(elze)
        val (noisyCond, dlts) = getNoisyExpr(cond, buddy, roundoffType)
        deltas = deltas ++ dlts
        IfExpr(noisyCond, thenNoisy, elseNoisy)

      case And(args) =>
        var esNoisy: Seq[Expr] = Seq.empty

        for (arg <- args) {
          val eNoisy = transformBody(arg)
          esNoisy = esNoisy :+ eNoisy
        }

        And(esNoisy)

      case UMinus(_) | Plus(_, _) | Minus(_, _) | Times(_, _) | Division(_, _) | FunctionInvocation(_, _) | Variable(_) =>
        val (rndExpr, dlts) = getNoisyExpr(e, buddy, roundoffType)
        deltas = deltas ++ dlts
        rndExpr

      case _ =>
        errors = errors :+ ("Unknown body! " + e);
        Error("unknown body: " + e).setType(BooleanType)
    }*/

}


