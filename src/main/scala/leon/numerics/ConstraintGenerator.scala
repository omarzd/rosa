package leon
package numerics

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

import collection.immutable.HashSet

class ConstraintGenerator(reporter:Reporter) {
  val verbose = false

  var deltaCounter = 0
  private def getNewDelta: Variable = {
    deltaCounter = deltaCounter + 1
    Variable(FreshIdentifier("#delta_" + deltaCounter))
  }

  private def getFreshRndoffMultiplier: (Expr, Variable) = {
    val delta = getNewDelta
    (Plus(new RationalLiteral(1), delta) , delta)
  }

  def constraintWithoutRoundoff(funDef: FunDef): FunctionConstraint = {
    val funName = funDef.id.name
    val pre = funDef.precondition
    val post = funDef.postcondition
    val body = funDef.body.get
    reporter.info("")
    reporter.info("-----> Analysing function " + funName + "...")
    if (verbose) {reporter.info("function body: " + body);  reporter.info("precondition: " + pre); reporter.info("postcondition: " + post)}


    // Separate input variables and local ones
    val resVar = Variable(FreshIdentifier("res")).setType(RealType)
    var funcVars: Map[Variable, Variable] =
      funDef.args.foldLeft(Map(resVar -> Variable(FreshIdentifier("#res_0")).setType(RealType)))(
        (map, nextArg) => map + (Variable(nextArg.id).setType(RealType) -> Variable(FreshIdentifier("#"+nextArg.id.name+"_0")).setType(RealType))
      )
    var localVars: Map[Variable, Variable] = allLetDefinitions(body).foldLeft(Map[Variable, Variable]())(
      (map, defpair) => map + (Variable(defpair._1).setType(RealType) ->
          Variable(FreshIdentifier("#"+defpair._1.name+"_0")).setType(RealType))
    )
    if (verbose) {reporter.info("func vars: %s, localVars: %s".format(funcVars, localVars))}


    // pre
    // TODO: check that inputs are constraint?
    val preConstraint: Expr = pre match {
      case Some(And(exprs)) => And(exprs.map(e => constraintFromSpec(e, funcVars, resVar)))
      case None => reporter.warning("Forgotten precondition?"); BooleanLiteral(true)
      case _ => reporter.warning("You've got a funny precondition: " + pre); BooleanLiteral(true)
    }
    if (verbose) reporter.info("preConstr: " + preConstraint)

    //body
    val (c1, c2) = bodyConstrNoRoundoff(body, funcVars ++ localVars, resVar)
    if (verbose) reporter.info("\nbody constr Real : " + c1)
    if (verbose) reporter.info("\nbody constr Noisy: " + c2)

    //post
    val postConstraint: Expr = post match {
      case Some(And(exprs)) => And(exprs.map(e => constraintFromSpec(e, funcVars, resVar)))
      case Some(expr) => constraintFromSpec(expr, funcVars, resVar) 
      case None => reporter.warning("Forgotten postcondition?"); BooleanLiteral(true)
      case _ => reporter.warning("You've got a funny postcondition: " + post);
        println(post.getClass)
        BooleanLiteral(true)
    }
    if (verbose) reporter.info("\npostConstr: " + postConstraint)
  
    val wholeConstraint = Implies(And(Seq(preConstraint, c1, c2)), postConstraint)
    if (verbose) reporter.info("\nwhole: " + wholeConstraint)

    new FunctionConstraint(funDef, wholeConstraint)
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
        LessEquals(new RationalLiteral(0), delta),
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
      val (rndExpr, deltas) = addRndoff(replace(buddy, expr))
      (Equals(res, expr), Equals(buddy(res), rndExpr))
   
    case _=>
      reporter.warning("Dropping instruction: " + expr + ". Cannot handle it.")
      println(expr.getClass)
      (BooleanLiteral(true), BooleanLiteral(true))
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

    case v: Variable => (v, List())
    case _=> (Error(""), List())    

  }
}
