package leon
package numerics

import ceres.common._

import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Definitions._
import purescala.Common._

object Analyser {
  
  // whether we consider also roundoff errors
  val withRoundoff = true

  private var deltaCounter = 0
  def getNewDelta: Variable = {
    deltaCounter = deltaCounter + 1
    Variable(FreshIdentifier("#delta_" + deltaCounter)).setType(RealType)
  }
  
  def getFreshRndoffMultiplier: (Expr, Variable) = {
    val delta = getNewDelta
    (Plus(new RationalLiteral(1), delta) , delta)
  }
  
  def constrainDeltas(deltas: List[Variable]): Expr = {
    val constraints = deltas.map(delta =>
      And(LessEquals(RationalLiteral(-unitRndoff), delta),
        LessEquals(delta, RationalLiteral(unitRndoff)))
      )
    And(constraints)
  }

  def getVariables(args: Seq[VarDecl], lets: List[(Identifier, Expr)]):
    (Variable, Map[Variable, Variable], Map[Variable, Variable]) = {
    val resVar = Variable(FreshIdentifier("res")).setType(RealType)

    var funcVars: Map[Variable, Variable] =
      args.foldLeft(Map(resVar -> Variable(FreshIdentifier("#res_0")).setType(RealType)))(
        (map, nextArg) => map + (Variable(nextArg.id).setType(RealType) -> Variable(FreshIdentifier("#"+nextArg.id.name+"_0")).setType(RealType))
      )
    var localVars: Map[Variable, Variable] = lets.foldLeft(Map[Variable, Variable]())(
      (map, defpair) => map + (Variable(defpair._1).setType(RealType) ->
          Variable(FreshIdentifier("#"+defpair._1.name+"_0")).setType(RealType))
    )
    (resVar, funcVars, localVars)
  }

}

class Analyser(reporter: Reporter) {
  import Analyser._

  val verbose = false

  def analyzeThis(funDef: FunDef): VerificationCondition = {
    reporter.info("")
    reporter.info("-----> Analysing function " + funDef.id.name + "...")

    val vc = new VerificationCondition(funDef)
    funDef.precondition match {
      case Some(p) =>
        vc.inputRanges = Utils.getVariableBounds(p)
        vc.precondition = Some(p)
      case None =>
        vc.precondition = Some(BooleanLiteral(true))
    }
    val body = funDef.body.get

    val start = System.currentTimeMillis
    val (resVar, funcVars, localVars) = getVariables(funDef.args, allLetDefinitions(body))

    
    val preConstraint: Expr = vc.precondition match {
      case Some(And(exprs)) => And(exprs.map(e => constraintFromSpec(e, funcVars, resVar)))
      case Some(expr) => constraintFromSpec(expr, funcVars, resVar)
      case None => reporter.warning("Forgotten precondition?"); BooleanLiteral(true)
      case _ => reporter.warning("You've got a funny precondition: " + vc.precondition); BooleanLiteral(true)
    } 
    if (verbose) reporter.info("preConstr: " + preConstraint)

    //body
    val (cIdeal, cActual) =
      if (!withRoundoff) bodyConstrNoRoundoff(body, funcVars ++ localVars, resVar)
      else {
        val (realC, noisyC, deltas) = bodyConstrWholeShebang(body, funcVars ++ localVars, resVar)
        (realC, And(noisyC, constrainDeltas(deltas)))
      }
    if (verbose) reporter.info("\nbody constr Real : " + cIdeal)
    if (verbose) reporter.info("\nbody constr Noisy: " + cActual)

    val postConstraint: Expr = funDef.postcondition match {
      case Some(And(exprs)) => And(exprs.map(e => constraintFromSpec(e, funcVars, resVar)))
      case Some(expr) => constraintFromSpec(expr, funcVars, resVar)
      case None => reporter.warning("Forgotten postcondition?"); BooleanLiteral(true)
      case _ => reporter.warning("You've got a funny postcondition: " + funDef.postcondition); BooleanLiteral(true)
    }

    vc.toCheck = vc.toCheck :+ Constraint(Implies(And(Seq(preConstraint, cIdeal, cActual)), postConstraint))

    vc.preConstraint = Some(preConstraint)
    vc.bodyConstraint = Some(And(cIdeal, cActual))
    vc.postConstraint = Some(postConstraint)

    // TODO: constraints for function calls, assertions and invariants

    val totalTime = (System.currentTimeMillis - start)
    vc.analysisTime = Some(totalTime)

    vc
  }


  // For now, this is all we allow
  private def constraintFromSpec(expr: Expr, buddy: Map[Variable, Variable], ress: Variable): Expr = expr match {
    case LessThan(Noise(v @ Variable(id)), r @ RationalLiteral(value)) =>
      LessThan(Abs(Minus(v, buddy(v))), r)

    case GreaterThan(r @ RationalLiteral(value), Noise(v @ Variable(id))) =>
      GreaterThan(r, Abs(Minus(v, buddy(v))))

    case LessEquals(Noise(v @ Variable(id)), r @ RationalLiteral(value)) =>
      LessEquals(Abs(Minus(v, buddy(v))), r)

    case GreaterEquals(r @ RationalLiteral(value), Noise(v @ Variable(id))) =>
      GreaterEquals(r, Abs(Minus(v, buddy(v))))

    case LessThan(Noise(ResultVariable()), r @ RationalLiteral(value)) =>
      LessThan(Abs(Minus(ress, buddy(ress))), r)

    case GreaterThan(r @ RationalLiteral(value), Noise(ResultVariable())) =>
      GreaterThan(r, Abs(Minus(ress, buddy(ress))))

    case LessEquals(Noise(ResultVariable()), r @ RationalLiteral(value)) =>
      LessEquals(Abs(Minus(ress, buddy(ress))), r)

    case GreaterEquals(r @ RationalLiteral(value), Noise(ResultVariable())) =>
      GreaterEquals(r, Abs(Minus(ress, buddy(ress))))

    case LessThan(_, Noise(_)) | GreaterThan(Noise(_), _) | LessEquals(_, Noise(_)) | GreaterEquals(Noise(_), _) =>
      reporter.warning("Doesn't make sense: " + expr)
      Error("Lower bounding noise").setType(RealType)

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
        LessEquals(RationalLiteral(-unitRndoff), delta),
        LessEquals(delta, RationalLiteral(unitRndoff))))

    case _=>
      reporter.warning("Dunno what to do with this: " + expr)
      Error("unknown constraint").setType(RealType)
  }

  // We could also do this path by path
  // And this may be doable with a Transformer from TreeOps
  private def bodyConstrNoRoundoff(expr: Expr, buddy: Map[Expr, Expr], res: Expr): (Expr, Expr) = expr match {
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
      reporter.warning("Dropping instruction: " + expr + ". Cannot handle it.")
      println(expr.getClass)
      (BooleanLiteral(true), BooleanLiteral(true))
  }

  // We separate the constraints on deltas from the rest for readability.
  //@return (real-valued constr, noisy constrs, deltas)
  private def bodyConstrWholeShebang(expr: Expr, buddy: Map[Expr, Expr], res: Expr):
    (Expr, Expr, List[Variable]) = expr match {
    case Let(id, valueExpr, rest) =>
      val letVar = Variable(id)
      val (restReal, restNoisy, restDeltas) = bodyConstrWholeShebang(rest, buddy, res)

      val (rndExpr, deltas) = addRndoff(replace(buddy, valueExpr))

      (And(Equals(letVar, valueExpr), restReal), And(Equals(buddy(letVar), rndExpr), restNoisy),
        restDeltas ++ deltas)

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
      reporter.warning("Dropping instruction: " + expr + ". Cannot handle it.")
      println(expr.getClass)
      (BooleanLiteral(true), BooleanLiteral(true), List())
  }


  // @return (constraint, deltas) (the expression with added roundoff, the deltas used)
  private def addRndoff(expr: Expr): (Expr, List[Variable]) = expr match {
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
      reporter.warning("Cannot add roundoff to: " + expr)
      (Error(""), List())

  }


  // It is complete, if the result is bounded below and above and the noise is specified.
/*  private def isComplete(post: Expr): Boolean = {
    post match {
      case and @ And(args) =>
        val variableBounds = Utils.getVariableBounds(and)
        val noise = TreeOps.contains(and, (
          a => a match {
            case Noise(ResultVariable()) => true
            case _ => false
          }))
        noise && variableBounds.contains(Variable(FreshIdentifier("#res")))

      case _ =>
        reporter.warning("Unsupported type of postcondition: " + post)
        false
    }
  }
*/

}
