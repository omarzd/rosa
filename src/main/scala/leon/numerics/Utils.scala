package leon
package numerics

import ceres.common._

import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Definitions._
import purescala.Common._


object Utils {
  def formatOption[T](res: Option[T]): String = res match {
    case Some(xf) => xf.toString
    case None => " -- "
  }


  case class Record(lo: Option[Rational], up: Option[Rational], noise: Option[Rational], rndoff: Option[Boolean]) {
    def updateLo(newLo: Rational): Record = Record(Some(newLo), up, noise, rndoff)
    def updateUp(newUp: Rational): Record = Record(lo, Some(newUp), noise, rndoff)
    def updateNoise(newNoise: Rational): Record = Record(lo, up, Some(newNoise), rndoff)
    def addRndoff: Record = Record(lo, up, noise, Some(true))

    override def toString: String = "[%s, %s] (%s)".format(
       formatOption(lo), formatOption(up), noise match {
         case Some(x) => x
         case None => "r"
       }
      )
  }
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

  // whether we consider also roundoff errors
  val withRoundoff = true

  private var deltaCounter = 0
  def getNewDelta: Variable = {
    deltaCounter = deltaCounter + 1
    Variable(FreshIdentifier("#delta_" + deltaCounter)).setType(RealType)
  }

  /*def getFreshRndoffMultiplier: (Expr, Variable) = {
    val delta = getNewDelta
    (Plus(new RationalLiteral(1), delta) , delta)
  }*/

  def getRndoff(expr: Expr): (Expr, Variable) = {
    val delta = getNewDelta
    (Times(expr, delta), delta)
  }

  def constrainDeltas(deltas: Seq[Variable], eps: Variable): Expr = {
    val constraints = deltas.map(delta =>
      And(LessEquals(UMinus(eps), delta),
        LessEquals(delta, eps))
      )
    And(constraints ++ Seq(Equals(eps, RationalLiteral(unitRndoff))))
  }

  def getVariables(args: Seq[VarDecl], lets: List[(Identifier, Expr)]):
    (Variable, Map[Variable, Variable], Map[Variable, Variable], Variable) = {
    val resVar = Variable(FreshIdentifier("res")).setType(RealType)
    val machineEps = Variable(FreshIdentifier("#eps")).setType(RealType)

    var funcVars: Map[Variable, Variable] =
      args.foldLeft(Map(resVar -> Variable(FreshIdentifier("#res_0")).setType(RealType)))(
        (map, nextArg) => map + (Variable(nextArg.id).setType(RealType) -> Variable(FreshIdentifier("#"+nextArg.id.name+"_0")).setType(RealType))
      )
    var localVars: Map[Variable, Variable] = lets.foldLeft(Map[Variable, Variable]())(
      (map, defpair) => map + (Variable(defpair._1).setType(RealType) ->
          Variable(FreshIdentifier("#"+defpair._1.name+"_0")).setType(RealType))
    )
    (resVar, funcVars, localVars, machineEps)
  }

  def exprToConstraint(funArgs: Seq[VarDecl], pre: Expr, body: Expr, post: Expr, reporter: Reporter): Expr = {
    val (resVar, funcVars, localVars, eps) = getVariables(funArgs, allLetDefinitions(body))

    val preConstraint: Expr = pre match {
      case And(exprs) => And(exprs.map(e => constraintFromSpec(e, funcVars, resVar, eps)))
      case expr => constraintFromSpec(expr, funcVars, resVar, eps)
      //case None => reporter.warning("Forgotten precondition?"); BooleanLiteral(true)
      //case _ => reporter.warning("You've got a funny precondition: " + vc.precondition); BooleanLiteral(true)
    }
    //if (verbose) reporter.info("preConstr: " + preConstraint)

    //body
    val (cIdeal, cActual) =
      //if (!withRoundoff) bodyConstrNoRoundoff(body, funcVars ++ localVars, resVar)
      //else {
        {
        val (realC, noisyC, deltas) = bodyConstrWholeShebang(body, funcVars ++ localVars, resVar)
        (realC, And(noisyC, constrainDeltas(deltas, eps)))
      }
      //}
    //if (verbose) reporter.info("\nbody constr Real : " + cIdeal)
    //if (verbose) reporter.info("\nbody constr Noisy: " + cActual)

    val postConstraint: Expr = post match {
      case And(exprs) => And(exprs.map(e => constraintFromSpec(e, funcVars, resVar, eps)))
      case expr => constraintFromSpec(expr, funcVars, resVar, eps)
      //case None => reporter.warning("Forgotten postcondition?"); BooleanLiteral(true)
      //case _ => reporter.warning("You've got a funny postcondition: " + funDef.postcondition); BooleanLiteral(true)
    }
    //if (verbose) reporter.info("postConstr: " + postConstraint)
    Implies(And(Seq(preConstraint, cIdeal, cActual)), postConstraint)

    //vc.preConstraint = Some(preConstraint)
    //vc.bodyConstraint = Some(And(cIdeal, cActual))
    //vc.postConstraint = Some(postConstraint)

  }



  // For now, this is all we allow
  def constraintFromSpec(expr: Expr, buddy: Map[Variable, Variable], ress: Variable, eps: Variable): Expr = expr match {
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




  // We could also do this path by path
  // And this may be doable with a Transformer from TreeOps
  /*private def bodyConstrNoRoundoff(expr: Expr, buddy: Map[Expr, Expr], res: Expr): (Expr, Expr) = expr match {
    case And(e1, e2) =>
      val (e1Real, )
      (And())

    case Equals()

    case Let(id, valueExpr, rest) =>
      val letVar = Variable(id)
      val (restReal, restNoisy) = bodyConstrNoRoundoff(rest, buddy, res)
      (And(Equals(letVar, valueExpr), restReal),
      And(Equals(buddy(letVar), replace(buddy, valueExpr)), restNoisy))

    case IfExpr(cond, then, elze) =>
      val (thenReal, thenNoisy) = bodyConstrNoRoundoff(then, buddy, res)
      val (elseReal, elseNoisy) = bodyConstrNoRoundoff(elze, buddy, res)

      val noisyCond = replace(buddy, cond)
      ( Or(And(cond, thenReal), And(Not(cond), elseReal)),
        Or(And(noisyCond, thenNoisy), And(Not(noisyCond), elseNoisy)))

    case UMinus(_) | Plus(_, _) | Minus(_, _) | Times(_, _) | Division(_, _) | FunctionInvocation(_, _) =>
      (Equals(res, expr), Equals(buddy(res), replace(buddy, expr)))

    case _=>
      println("Dropping instruction: " + expr + ". Cannot handle it.")
      println(expr.getClass)
      (BooleanLiteral(true), BooleanLiteral(true))
  }*/

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
      val (valueExprNoisy, deltas) = addRndoff(replace(buddy, valueExpr))
      (Equals(v, valueExpr), Equals(buddy(v), valueExprNoisy), deltas)

    /*case Let(id, valueExpr, rest) =>
      val letVar = Variable(id)
      val (restReal, restNoisy, restDeltas) = bodyConstrWholeShebang(rest, buddy, res)

      val (rndExpr, deltas) = addRndoff(replace(buddy, valueExpr))

      (And(Equals(letVar, valueExpr), restReal), And(Equals(buddy(letVar), rndExpr), restNoisy),
        restDeltas ++ deltas)*/

    case IfExpr(cond, then, elze) =>
      val (thenReal, thenNoisy, thenDeltas) = bodyConstrWholeShebang(then, buddy, res)
      val (elseReal, elseNoisy, elseDeltas) = bodyConstrWholeShebang(elze, buddy, res)

      val (noisyCond, deltas) = addRndoff(replace(buddy, cond))
      ( Or(And(cond, thenReal), And(Not(cond), elseReal)),
        Or(And(noisyCond, thenNoisy), And(Not(noisyCond), elseNoisy)),
        thenDeltas ++ elseDeltas ++ deltas)

    case UMinus(_) | Plus(_, _) | Minus(_, _) | Times(_, _) | Division(_, _) | FunctionInvocation(_, _) =>
      val (rndExpr, deltas) = addRndoff(replace(buddy, expr))
      (Equals(res, expr), Equals(buddy(res), rndExpr), deltas)

    case _=>
      println("Dropping instruction: " + expr + ". Cannot handle it.")
      println(expr.getClass)
      (BooleanLiteral(true), BooleanLiteral(true), List())
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


}
