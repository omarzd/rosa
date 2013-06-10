package leon
package numerics

import ceres.common._

import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Definitions._
import purescala.Common._

import affine.XFloat


object Utils {
  def formatOption[T](res: Option[T]): String = res match {
    case Some(xf) => xf.toString
    case None => " -- "
  }

  /* ################################

      Collecting variable ranges and noises.

  ################################### */

  val emptyRecord = Record(None, None, None, None)

  class VariableCollector extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil
    var recordMap: Map[Variable, Record] = Map.empty

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      // a <= x
      case LessEquals(RationalLiteral(lwrBnd), x @ Variable(name)) =>
        recordMap = recordMap + (x -> recordMap.getOrElse(x, emptyRecord).updateLo(lwrBnd)); e
      // x <= b
      case LessEquals(x @ Variable(name), RationalLiteral(uprBnd)) =>
        recordMap = recordMap + (x -> recordMap.getOrElse(x, emptyRecord).updateUp(uprBnd)); e
      // a <= x
      case LessEquals(IntLiteral(lwrBnd), x @ Variable(name)) =>
        recordMap = recordMap + (x -> recordMap.getOrElse(x, emptyRecord).updateLo(Rational(lwrBnd))); e
      // x <= b
      case LessEquals(x @ Variable(name), IntLiteral(uprBnd)) =>
        recordMap = recordMap + (x -> recordMap.getOrElse(x, emptyRecord).updateUp(Rational(uprBnd))); e

      // b >= x
      case GreaterEquals(RationalLiteral(uprBnd), x @ Variable(name)) =>
        recordMap = recordMap + (x -> recordMap.getOrElse(x, emptyRecord).updateUp(uprBnd)); e
      // x >= a
      case GreaterEquals(x @ Variable(name), RationalLiteral(lwrBnd)) =>
        recordMap = recordMap + (x -> recordMap.getOrElse(x, emptyRecord).updateLo(lwrBnd)); e
      // b >= x
      case GreaterEquals(IntLiteral(uprBnd), x @ Variable(name)) =>
        recordMap = recordMap + (x -> recordMap.getOrElse(x, emptyRecord).updateUp(Rational(uprBnd))); e
      // x >= a
      case GreaterEquals(x @ Variable(name), IntLiteral(lwrBnd)) =>
        recordMap = recordMap + (x -> recordMap.getOrElse(x, emptyRecord).updateLo(Rational(lwrBnd))); e

      case Noise(x @ Variable(id), RationalLiteral(value)) =>
        recordMap = recordMap + (x -> recordMap.getOrElse(x, emptyRecord).updateNoise(value)); e

      case Noise(x @ Variable(id), IntLiteral(value)) =>
        recordMap = recordMap + (x -> recordMap.getOrElse(x, emptyRecord).updateNoise(Rational(value))); e

      case Roundoff(x @ Variable(id)) =>
        recordMap = recordMap + (x -> recordMap.getOrElse(x, emptyRecord).addRndoff); e

      case _ =>
        super.rec(e, path)
    }

  }

  /* #################################

      Converting expressions to constraints.

     ################################# */

  // whether we consider also roundoff errors and how we translate them into constraints
  import RoundoffType._
  // TODO: this should not be a global variable
  val roundoffType: RoundoffType = RoundoffMultiplier


  def exprToConstraint(variables: Seq[Variable], pre: Expr, body: Expr, post: Expr, reporter: Reporter): Expr = {
    val (resVar, eps, allVars) = getVariables(variables)

    val preConstraint: Expr = pre match {
      case And(exprs) => And(exprs.map(e => constraintFromSpec(e, allVars, resVar, eps)))
      case expr => constraintFromSpec(expr, allVars, resVar, eps)
    }

    //body
    val (cIdeal, noisyC, deltas) = bodyConstrWholeShebang(body, allVars, resVar)
    val cActual = And(noisyC, constrainDeltas(deltas, eps))

    val postConstraint: Expr = post match {
      case And(exprs) => And(exprs.map(e => constraintFromSpec(e, allVars, resVar, eps)))
      case expr => constraintFromSpec(expr, allVars, resVar, eps)
    }
    Implies(And(Seq(preConstraint, cIdeal, cActual)), postConstraint)
  }

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

  private def getVariables(variables: Seq[Variable]): (Variable, Variable, Map[Expr, Expr]) = {
    val resVar = Variable(FreshIdentifier("res")).setType(RealType)
    val machineEps = Variable(FreshIdentifier("#eps")).setType(RealType)

    var buddies: Map[Expr, Expr] =
      variables.foldLeft(Map[Expr, Expr](resVar -> Variable(FreshIdentifier("#res_0")).setType(RealType)))(
        (map, nextVar) => map + (nextVar -> Variable(FreshIdentifier("#"+nextVar.id.name+"_0")).setType(RealType))
      )

    (resVar, machineEps, buddies)
  }


  // For now, this is all we allow
  private def constraintFromSpec(expr: Expr, buddy: Map[Expr, Expr], ress: Variable, eps: Variable): Expr = expr match {
    case Noise(v @ Variable(id), r @ RationalLiteral(value)) =>
      if (value < Rational.zero) {
        println("Noise must be positive.")
        Error("negative noise").setType(BooleanType)
      } else {
        LessEquals(Abs(Minus(v, buddy(v))), r)
      }

    case Noise(ResultVariable(), r @ RationalLiteral(value)) =>
      if (value < Rational.zero) {
        println("Noise must be positive.")
        Error("negative noise").setType(BooleanType)
      } else {
        LessEquals(Abs(Minus(ress, buddy(ress))), r)
      }

    case LessThan(Variable(_), RationalLiteral(_)) | LessThan(RationalLiteral(_), Variable(_)) => expr
    case LessEquals(Variable(_), RationalLiteral(_)) | LessEquals(RationalLiteral(_), Variable(_)) => expr
    case GreaterThan(Variable(_), RationalLiteral(_)) | GreaterThan(RationalLiteral(_), Variable(_)) => expr
    case GreaterEquals(Variable(_), RationalLiteral(_)) | GreaterEquals(RationalLiteral(_), Variable(_)) => expr

    case LessThan(ResultVariable(), RationalLiteral(_)) | LessThan(RationalLiteral(_), ResultVariable()) => replace(Map(ResultVariable() -> ress), expr)
    case LessEquals(ResultVariable(), RationalLiteral(_)) | LessEquals(RationalLiteral(_), ResultVariable()) => replace(Map(ResultVariable() -> ress), expr)
    case GreaterThan(ResultVariable(), RationalLiteral(_)) | GreaterThan(RationalLiteral(_), ResultVariable()) => replace(Map(ResultVariable() -> ress), expr)
    case GreaterEquals(ResultVariable(), RationalLiteral(_)) | GreaterEquals(RationalLiteral(_), ResultVariable()) => replace(Map(ResultVariable() -> ress), expr)

    case Roundoff(v @ Variable(id)) =>
      val delta = getNewDelta
      And(Seq(Equals(buddy(v), Times(Plus(new RationalLiteral(1), delta), v)),
        LessEquals(UMinus(eps), delta),
        LessEquals(delta, eps)))

    case _=>
      println("Dunno what to do with this: " + expr)
      Error("unknown constraint").setType(BooleanType)
  }

  // We separate the constraints on deltas from the rest for readability.
  //@return (real-valued constr, noisy constrs, deltas)
  private def bodyConstrWholeShebang(expr: Expr, buddy: Map[Expr, Expr], res: Expr):
    (Expr, Expr, Seq[Variable]) = expr match {
    case And(es) =>
      var esReal: Seq[Expr] = Seq.empty
      var esNoisy: Seq[Expr] = Seq.empty
      var deltas: Seq[Variable] = List.empty

      for (e <- es) {
        val (eReal, eNoisy, eDelta) = bodyConstrWholeShebang(e, buddy, res)
        esReal = esReal :+ eReal
        esNoisy = esNoisy :+ eNoisy
        deltas = deltas ++ eDelta
      }

      (And(esReal), And(esNoisy), deltas)

    case Equals(v @ Variable(id), valueExpr) =>
      val (valueExprNoisy, deltas) = getNoisyExpr(valueExpr, buddy, roundoffType)
      (Equals(v, valueExpr), Equals(buddy(v), valueExprNoisy), deltas)

    case IfExpr(cond, then, elze) =>
      val (thenReal, thenNoisy, thenDeltas) = bodyConstrWholeShebang(then, buddy, res)
      val (elseReal, elseNoisy, elseDeltas) = bodyConstrWholeShebang(elze, buddy, res)

      val (noisyCond, deltas) = getNoisyExpr(cond, buddy, roundoffType)
      ( Or(And(cond, thenReal), And(Not(cond), elseReal)),
        Or(And(noisyCond, thenNoisy), And(Not(noisyCond), elseNoisy)),
        thenDeltas ++ elseDeltas ++ deltas)

    case UMinus(_) | Plus(_, _) | Minus(_, _) | Times(_, _) | Division(_, _) | FunctionInvocation(_, _) =>
      val (rndExpr, deltas) = getNoisyExpr(expr, buddy, roundoffType)
      (Equals(res, expr), Equals(buddy(res), rndExpr), deltas)

    case _=>
      println("Dropping instruction: " + expr + ". Cannot handle it.")
      println(expr.getClass)
      (BooleanLiteral(true), BooleanLiteral(true), List())
  }

  private def getNoisyExpr(expr: Expr, buddy: Map[Expr, Expr], rndoff: RoundoffType): (Expr, List[Variable]) = roundoffType match {
    case NoRoundoff => (replace(buddy, expr), List())
    case RoundoffMultiplier => addRndoff2(replace(buddy, expr))
    case RoundoffAddition => addRndoff(replace(buddy, expr))
  }


  private def getFreshRndoffMultiplier: (Expr, Variable) = {
    val delta = getNewDelta
    (Plus(new RationalLiteral(1), delta) , delta)
  }

  private def getRndoff(expr: Expr): (Expr, Variable) = {
    val delta = getNewDelta
    (Times(expr, delta), delta)
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

}
