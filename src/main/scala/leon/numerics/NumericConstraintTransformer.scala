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

class NumericConstraintTransformer(buddy: Map[Expr, Expr], ress: Variable, eps: Variable,
  roundoffType: RoundoffType, reporter: Reporter) {

  var errors: Seq[String] = Seq.empty
  var extraConstraints: Seq[Expr] = Seq.empty

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
        val freshErrorVar = getErrorVar(v)
        And(Seq(Equals(buddy(v), Plus(v, freshErrorVar)),
          LessEquals(RationalLiteral(-value), freshErrorVar), 
          LessEquals(freshErrorVar, RationalLiteral(value))))
      }
    case Noise(ResultVariable(), r @ RationalLiteral(value)) =>
      if (value < Rational.zero) { errors = errors :+ "Noise must be positive."; Error("negative noise " + value).setType(BooleanType)
      } else {
        val freshErrorVar = getErrorVar(ress)
        And(Seq(Equals(buddy(ress), Plus(ress, freshErrorVar)),
          LessEquals(RationalLiteral(-value), freshErrorVar), 
          LessEquals(freshErrorVar, RationalLiteral(value))))
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

    case Plus(x, y) => Plus(transformPrePost(x), transformPrePost(y))
    case Minus(x, y) => Minus(transformPrePost(x), transformPrePost(y))
    case Times(x, y) => Times(transformPrePost(x), transformPrePost(y))
    case Division(x, y) => Division(transformPrePost(x), transformPrePost(y))
    case UMinus(x) => UMinus(transformPrePost(x))

    case Sqrt(x) =>
      val r = getNewSqrtVariable
      val xR = transformPrePost(x)
      extraConstraints ++= Seq(Equals(Times(r, r), xR), LessEquals(RationalLiteral(zero), r))
      r
    case Equals(l, r) => Equals(transformPrePost(l), transformPrePost(r))

    case a @ Actual(v @ Variable(id)) => buddy(v)
    case Actual(ResultVariable()) => buddy(ress)

    case Actual(x) => reporter.error("Actual only allowed on variables, but not on: " + x.getClass); e
    case ResultVariable() => ress
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
      And(args.foldLeft(Seq[Expr]())( (seq, arg) => seq :+ transformIdealBody(arg) ))

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
      And(args.foldLeft(Seq[Expr]())( (seq, arg) => seq :+ transformNoisyBody(arg) ))
      
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
}


