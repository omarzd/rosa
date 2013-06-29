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

class NumericConstraintTransformer(buddy: Map[Expr, Expr], ress: Variable, eps: Variable,
  roundoffType: RoundoffType, reporter: Reporter) {

    var errors: Seq[String] = Seq.empty
    var extraConstraints: Seq[Expr] = Seq.empty

    def addExtra(e: Expr) = extraConstraints = extraConstraints :+ e

    def init = {
      errors = Seq.empty
      extraConstraints = Seq[Equals]()//Seq(Equals(eps, RationalLiteral(unitRndoff)))
    }

    def printErrors = for (err <- errors) reporter.error(err)


    def transformBlock(body: Expr): (Expr, Expr) = {
      init
      val (bodyCReal, bodyCNoisy) = transformBody(body)
      printErrors
      (bodyCReal, And(Seq(bodyCNoisy) ++ extraConstraints))
    }

    def transformIdealBlock(body: Expr): Expr = {
      init
      val newBody = transformIdealBody(body)
      printErrors
      And(Seq(newBody) ++ extraConstraints)
    }

    def transformNoisyBlock(body: Expr): Expr = {
      init
      val newBody = transformNoisyBody(body)
      printErrors
      And(Seq(newBody) ++ extraConstraints)
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

      case LessThan(x, y) => LessThan(transformPrePost(x), transformPrePost(y))
      case GreaterThan(x, y) => GreaterThan(transformPrePost(x), transformPrePost(y))
      case LessEquals(x, y) => LessEquals(transformPrePost(x), transformPrePost(y))
      case GreaterEquals(x, y) => GreaterEquals(transformPrePost(x), transformPrePost(y))

      case a @ Actual(v @ Variable(id)) => buddy(v)
      case Actual(ResultVariable()) => buddy(ress)

      case Actual(x) => reporter.error("Actual only allowed on variables, but not on: " + x.getClass); e

      /*case MorePrecise(x @ Variable(id1), y @ Variable(id2)) =>
        val x0 = buddy(x)
        val y0 = buddy(y)
        val y0_y = Minus(y0, y)
        val y_y0 = Minus(y, y0)
        val x0_x = Minus(x0, x)
        val x_x0 = Minus(x, x0)
        And(Seq(
          LessEquals(y0_y, x_x0), LessEquals(y_y0, x_x0),
          LessEquals(x_x0, y_y0), LessEquals(x_x0, y0_y)
          ))

      case MorePrecise(x, y) =>
        reporter.error("MorePrecise only allowed on variables, but not on: " + x.getClass + ", " + y.getClass); e
      */
      case _ => e
    }

  def transformIdealBody(e: Expr): Expr = e match {
    case Equals(v @ Variable(id), valueExpr) =>
      val real = transformIdealBody(valueExpr)
      Equals(v, real)

    case Equals(ResultVariable(), valueExpr) =>
      val real = transformIdealBody(valueExpr)
      Equals(ress, real)

    case IfExpr(cond, then, elze) =>
      val thenR = transformIdealBody(then)
      val elseR = transformIdealBody(elze)
      val realC = transformIdealBody(cond)
      IfExpr(realC, thenR, elseR)

    case And(args) =>
      //var esReal: Seq[Expr] = Seq.empty

      val esReal = args.foldLeft(Seq[Expr]())( (seq, arg) => seq :+ transformIdealBody(arg) )
      /*for (arg <- args) {
        val eReal = transformIdealBody(arg)
        esReal = esReal :+ eReal
      }*/
      And(esReal)

    case Plus(x, y) => Plus(transformIdealBody(x), transformIdealBody(y))
    case Minus(x, y) => Minus(transformIdealBody(x), transformIdealBody(y))
    case Times(x, y) => Times(transformIdealBody(x), transformIdealBody(y))
    case Division(x, y) => Division(transformIdealBody(x), transformIdealBody(y))
    case UMinus(x) => UMinus(transformIdealBody(x))

    case Sqrt(x) =>
      val r = getNewSqrtVariable
      val xR = transformIdealBody(x)
      extraConstraints ++= Seq(Equals(Times(r, r), xR), LessEquals(RationalLiteral(zero), r))
      r

    case LessEquals(x, y) => LessEquals(transformIdealBody(x), transformIdealBody(y))
    case LessThan(x, y) => LessThan(transformIdealBody(x), transformIdealBody(y))
    case GreaterEquals(x, y) => GreaterEquals(transformIdealBody(x), transformIdealBody(y))
    case GreaterThan(x, y) => GreaterThan(transformIdealBody(x), transformIdealBody(y))
    case v: Variable => v
    case r: RationalLiteral => r
    case fnc @ FunctionInvocation(funDef, args) => fnc
    case BooleanLiteral(true) => BooleanLiteral(true)
    case _ =>
      errors = errors :+ ("Unknown body! " + e);
      Error("unknown body: " + e).setType(BooleanType)
  }

  def transformNoisyBody(e: Expr): Expr = e match {
    case Equals(v @ Variable(id), valueExpr) =>
      val noisy = transformNoisyBody(valueExpr)
      Equals(buddy(v), noisy)

    case Equals(ResultVariable(), valueExpr) =>
      val noisy = transformNoisyBody(valueExpr)
      Equals(buddy(ress), noisy)

    case IfExpr(cond, then, elze) =>
      val thenN = transformNoisyBody(then)
      val elseN = transformNoisyBody(elze)
      val noisyC = transformNoisyBody(cond)
      IfExpr(noisyC, thenN, elseN)

    case And(args) =>
      val esReal = args.foldLeft(Seq[Expr]())( (seq, arg) => seq :+ transformNoisyBody(arg) )
      /*for (arg <- args) {
        val eReal = transformIdealBody(arg)
        esReal = esReal :+ eReal
      }*/
      And(esReal)
      /*var esReal: Seq[Expr] = Seq.empty
      var esNoisy: Seq[Expr] = Seq.empty

      for (arg <- args) {
        val (eReal, eNoisy) = transformNoisyBody(arg)
        esReal = esReal :+ eReal
        esNoisy = esNoisy :+ eNoisy
      }
      (And(esReal), And(esNoisy))*/

    case Plus(x, y) =>
      val (mult, dlt) = getFreshRndoffMultiplier
      addExtra(constrainDelta(dlt))
      Times(Plus(transformNoisyBody(x), transformNoisyBody(y)), mult)

    case Minus(x, y) =>
      val (mult, dlt) = getFreshRndoffMultiplier
      addExtra(constrainDelta(dlt))
      Times(Minus(transformNoisyBody(x), transformNoisyBody(y)), mult)

    case Times(x, y) =>
      val (mult, dlt) = getFreshRndoffMultiplier
      addExtra(constrainDelta(dlt))
      Times(Times(transformNoisyBody(x), transformNoisyBody(y)), mult)

    case Division(x, y) =>
      val (mult, dlt) = getFreshRndoffMultiplier
      addExtra(constrainDelta(dlt))
      Times(Division(transformNoisyBody(x), transformNoisyBody(y)), mult)

    case UMinus(x) => UMinus(transformNoisyBody(x))

    case Sqrt(x) =>
      val n = getNewSqrtVariable
      val (mult, dlt) = getFreshRndoffMultiplier
      addExtra(constrainDelta(dlt))
      val xN = transformNoisyBody(x)
      extraConstraints ++= Seq(Equals(Times(n, n), xN), LessEquals(RationalLiteral(zero), n))
      Times(n, mult)

    case LessEquals(x, y) => LessEquals(transformNoisyBody(x), transformNoisyBody(y))
    case LessThan(x, y) => LessThan(transformNoisyBody(x), transformNoisyBody(y))
    case GreaterEquals(x, y) => GreaterEquals(transformNoisyBody(x), transformNoisyBody(y))
    case GreaterThan(x, y) => GreaterThan(transformNoisyBody(x), transformNoisyBody(y))
    case v: Variable => buddy(v)

    case r @ RationalLiteral(v) =>
      if (isExact(v)) r
      else {
        val (mult, dlt) = getFreshRndoffMultiplier
        addExtra(constrainDelta(dlt))
        Times(r, mult)
      }
    case fnc @ FunctionInvocation(funDef, args) =>
      FunctionInvocation(funDef, args.map(a => buddy(a)))

    case BooleanLiteral(true) => BooleanLiteral(true)
    case _ =>
      errors = errors :+ ("Unknown body! " + e);
      Error("unknown body: " + e).setType(BooleanType)
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
      val (r, n) = getNewSqrtVariablePair
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

    case r @ RationalLiteral(v) =>
      if (isExact(v)) (r, r)
      else {
        val (mult, dlt) = getFreshRndoffMultiplier
        addExtra(constrainDelta(dlt))
        (r, Times(r, mult))
      }
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


