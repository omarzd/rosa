package leon
package numerics

import ceres.common._

import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Definitions._
import purescala.Common._
import Utils._
import ArithmeticOps._

class Analyser(reporter: Reporter) {

  val verbose = false

  def analyzeThis(funDef: FunDef): VerificationCondition = {
    if (verbose) reporter.info("")
    if (verbose) reporter.info("-----> Analysing function " + funDef.id.name + "...")
    if (verbose) println("pre: " + funDef.precondition)
    if (verbose) println("\nbody: " + funDef.body)
    if (verbose) println("\npost: " + funDef.postcondition)

    val vc = new VerificationCondition(funDef)
    funDef.precondition match {
      case Some(p) =>
        vc.inputs = getVariableRecords(p)
        if (verbose) reporter.info("inputs: " + vc.inputs)
        val impliedRndoff = vc.inputs.collect { case (k, Record(_, _, None, None)) =>  Roundoff(k) }
        vc.precondition = Some(And(p, And(impliedRndoff.toSeq)))
        vc.allFncCalls ++= functionCallsOf(p).map(invc => invc.funDef.id.toString)
      case None =>
        vc.precondition = Some(BooleanLiteral(true))
    }

    vc.allFncCalls ++= functionCallsOf(funDef.body.get).map(invc => invc.funDef.id.toString)
    vc.isInvariant = funDef.returnType == BooleanType

    var bodyProcessed = funDef.postcondition match {
      //invariant
      case Some(ResultVariable()) =>
        val postConditions = getInvariantCondition(funDef.body.get)
        val bodyWOLets = convertLetsToEquals(funDef.body.get)
        vc.body = Some(replace(postConditions.map(p => (p, BooleanLiteral(true))).toMap, bodyWOLets))
        vc.allConstraints = List(Constraint(vc.precondition.get, vc.body.get, Or(postConditions), "wholebody"))
        bodyWOLets
      // 'Normal' function R^n -> R
      case Some(post) =>
        vc.body = Some(convertLetsToEquals(addResult(funDef.body.get)))
        val specC = Constraint(vc.precondition.get, vc.body.get, post, "wholeBody")
        vc.allConstraints = List(specC)
        vc.allFncCalls ++= functionCallsOf(post).map(invc => invc.funDef.id.toString)
        vc.body.get
      // Auxiliary function, nothing to prove
      case None =>
        if (vc.isInvariant) reporter.warning("Forgotten holds on invariant " + funDef.id + "?")
        vc.body = Some(convertLetsToEquals(addResult(funDef.body.get)))
        vc.body.get
    }

    if (containsFunctionCalls(bodyProcessed)) {
      val noiseRemover = new NoiseRemover
      val paths = collectPaths(bodyProcessed)
      for (path <- paths) {
        var i = 0
        while (i != -1) {
          val j = path.expression.indexWhere(e => containsFunctionCalls(e), i)
          if (j != -1) {
            i = j + 1
            val pathToFncCall = path.expression.take(j)
            val fncCalls = functionCallsOf(path.expression(j))
            for (fncCall <- fncCalls) {
              fncCall.funDef.precondition match {
                case Some(p) =>
                  val args: Map[Expr, Expr] = fncCall.funDef.args.map(decl => decl.toVariable).zip(fncCall.args).toMap
                  val postcondition = replace(args, noiseRemover.transform(p))
                  vc.allConstraints = vc.allConstraints :+ Constraint(
                      And(vc.precondition.get, path.condition), And(pathToFncCall), postcondition, "pre of call " + fncCall.toString)
                case None => ;
              }
            }
          } else { i = -1}
        }
      }

    }
    //println("all fncCalls: " + vc.allFncCalls)
    //println("All constraints generated: ")
    //println(vc.allConstraints.mkString("\n -> ") )

    vc.funcArgs = vc.funDef.args.map(v => Variable(v.id).setType(RealType))
    vc.localVars = allLetDefinitions(funDef.body.get).map(letDef => Variable(letDef._1).setType(RealType))

    vc
  }

  // Has to run before we removed the lets!
  // Basically the first free expression that is not an if or a let is the result
  private def addResult(expr: Expr): Expr = expr match {
    case IfExpr(cond, then, elze) => IfExpr(cond, addResult(then), addResult(elze))
    case Let(binder, value, body) => Let(binder, value, addResult(body))
    case UMinus(_) | Plus(_, _) | Minus(_, _) | Times(_, _) | Division(_, _) | Sqrt(_) | FunctionInvocation(_, _) | Variable(_) =>
      Equals(ResultVariable(), expr)
    case _ => expr
  }

  // can return several, as we may have an if-statement
  private def getInvariantCondition(expr: Expr): List[Expr] = expr match {
    case IfExpr(cond, then, elze) => getInvariantCondition(then) ++ getInvariantCondition(elze)
    case Let(binder, value, body) => getInvariantCondition(body)
    case LessEquals(_, _) | LessThan(_, _) | GreaterThan(_, _) | GreaterEquals(_, _) => List(expr)
    case Equals(_, _) => List(expr)
    case _ =>
      reporter.error("Expected invariant, but found: " + expr.getClass)
      List(BooleanLiteral(false))
  }

  private def convertLetsToEquals(expr: Expr): Expr = expr match {
    case IfExpr(cond, then, elze) =>
      IfExpr(cond, convertLetsToEquals(then), convertLetsToEquals(elze))

    case Let(binder, value, body) =>
      And(Equals(Variable(binder), convertLetsToEquals(value)), convertLetsToEquals(body))

    case _ => expr

  }



  

}
