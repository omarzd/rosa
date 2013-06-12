package leon
package numerics

import ceres.common._

import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Definitions._
import purescala.Common._

import RoundoffType._

object NumericConstraintTransformer {

  private var deltaCounter = 0
  def getNewDelta: Variable = {
    deltaCounter = deltaCounter + 1
    Variable(FreshIdentifier("#delta_" + deltaCounter)).setType(RealType)
  }

  private def constrainDeltas(deltas: Seq[Variable], eps: Variable): Expr = {
    val constraints = deltas.map(delta =>
      And(LessEquals(UMinus(eps), delta),
        LessEquals(delta, eps))
      )
    And(constraints ++ Seq(Equals(eps, RationalLiteral(unitRndoff))))
  }

 private def getRndoff(expr: Expr): (Expr, Variable) = {
    val delta = getNewDelta
    (Times(expr, delta), delta)
  }

  private def getFreshRndoffMultiplier: (Expr, Variable) = {
    val delta = getNewDelta
    (Plus(new RationalLiteral(1), delta) , delta)
  }


}


  // TODO: eps needs to be only defined once...
class NumericConstraintTransformer(buddy: Map[Expr, Expr], ress: Variable, eps: Variable,
  roundoffType: RoundoffType, reporter: Reporter) {
  import NumericConstraintTransformer._

    var errors: Seq[String] = Seq.empty
    var deltas: Seq[Variable] = Seq.empty

    def printErrors = {
      for (err <- errors)
        reporter.error(err)
    }

    // TODO print the errors!
    def transformBlock(body: Expr): (Expr, Expr) = {
      errors = Seq.empty
      deltas = Seq.empty
      val (bodyCReal, bodyCNoisy) = transformBody(body)
      printErrors
      (bodyCReal, And(bodyCNoisy, constrainDeltas(deltas, eps)))
    }

    def transformCondition(cond: Expr): Expr = {
      errors = Seq.empty
      deltas = Seq.empty
      val condC = cond match {
        case And(args) => args.map(p => transformSingleCondition(p))
        case _ => Seq(transformSingleCondition(cond))
      }
      printErrors
      And(condC ++ Seq(constrainDeltas(deltas, eps)))
    }

    def getNoisyCondition(e: Expr): Expr = {
      replace(buddy, e)
    }

    def transformSingleCondition(e: Expr): Expr = e match {
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
        deltas = deltas :+ delta
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
        val (thenReal, thenNoisy) = transformBody(then)
        val (elseReal, elseNoisy) = transformBody(elze)
        val (noisyCond, dlts) = getNoisyExpr(cond)
        deltas = deltas ++ dlts
        (IfExpr(cond, then, elze), IfExpr(noisyCond, thenNoisy, elseNoisy))
      
      case And(args) =>
        var esReal: Seq[Expr] = Seq.empty
        var esNoisy: Seq[Expr] = Seq.empty

        for (arg <- args) {
          val (eReal, eNoisy) = transformBody(arg)
          esReal = esReal :+ eReal
          esNoisy = esNoisy :+ eNoisy
        }

        (And(esReal), And(esNoisy))

      case UMinus(_) | Plus(_, _) | Minus(_, _) | Times(_, _) | Division(_, _) | FunctionInvocation(_, _) | Variable(_) =>
        val (rndExpr, dlts) = getNoisyExpr(e)
        deltas = deltas ++ dlts
        (e, rndExpr)

      case _ =>
        errors = errors :+ ("Unknown body! " + e);
        (Error("unknown body: " + e).setType(BooleanType), Error("unknown body: " + e).setType(BooleanType))
    }

  private def getNoisyExpr(expr: Expr): (Expr, List[Variable]) = roundoffType match {
    case NoRoundoff => (replace(buddy, expr), List())
    case RoundoffMultiplier => addRndoff2(replace(buddy, expr))
    case RoundoffAddition => addRndoff(replace(buddy, expr))
  }
    
   // @return (constraint, deltas) (the expression with added roundoff, the deltas used)
  private def addRndoff(expr: Expr): (Expr, List[Variable]) = expr match {
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

  }

  // This uses the roundoff multiplier version
  private def addRndoff2(expr: Expr): (Expr, List[Variable]) = expr match {
    case Plus(x, y) =>
      val (mult, delta) = getFreshRndoffMultiplier
      val (xExpr, xDeltas) = addRndoff(x)
      val (yExpr, yDeltas) = addRndoff(y)
      (Times(Plus(xExpr, yExpr), mult), xDeltas ++ yDeltas ++ List(delta))

    case Minus(x, y) =>
      val (mult, delta) = getFreshRndoffMultiplier
      val (xExpr, xDeltas) = addRndoff(x)
      val (yExpr, yDeltas) = addRndoff(y)
      (Times(Minus(xExpr, yExpr), mult), xDeltas ++ yDeltas ++ List(delta))

    case Times(x, y) =>
      val (mult, delta) = getFreshRndoffMultiplier
      val (xExpr, xDeltas) = addRndoff(x)
      val (yExpr, yDeltas) = addRndoff(y)
      (Times(Times(xExpr, yExpr), mult), xDeltas ++ yDeltas ++ List(delta))

    case Division(x, y) =>
      val (mult, delta) = getFreshRndoffMultiplier
      val (xExpr, xDeltas) = addRndoff(x)
      val (yExpr, yDeltas) = addRndoff(y)
      (Times(Division(xExpr, yExpr), mult), xDeltas ++ yDeltas ++ List(delta))

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

  }

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


