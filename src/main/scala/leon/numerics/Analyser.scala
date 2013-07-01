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
import xlang.Trees._

class Analyser(reporter: Reporter) {

  val verbose = true
  val assertionRemover = new AssertionRemover


  def analyzeThis(funDef: FunDef): VerificationCondition = {
    if (verbose) reporter.info("")
    if (verbose) reporter.info("-----> Analysing function " + funDef.id.name + "...")
    if (verbose) println("pre: " + funDef.precondition)
    if (verbose) println("\nbody: " + funDef.body)
    if (verbose) println("\npost: " + funDef.postcondition)

    var allFncCalls = Set[String]()
    var constraints = List[Constraint]()

    val (inputVariables, vcPrecondition) = funDef.precondition match {
      case Some(p) =>
        val inputs = getVariableRecords(p)
        if (verbose) reporter.info("inputs: " + inputs)
        val impliedRndoff = inputs.collect { case (k, Record(_, _, None, None)) =>  Roundoff(k) }
        allFncCalls ++= functionCallsOf(p).map(invc => invc.funDef.id.toString)
        (inputs, And(p, And(impliedRndoff.toSeq)))
      case None =>
        (Map[Variable, Record](), True)
    }

    allFncCalls ++= functionCallsOf(funDef.body.get).map(invc => invc.funDef.id.toString)

    var (bodyProcessed, vcBody) = funDef.postcondition match {
      //invariant
      case Some(ResultVariable()) =>
        val postConditions = getInvariantCondition(funDef.body.get)
        val bodyWOLets = convertLetsToEquals(funDef.body.get)
        val body = replace(postConditions.map(p => (p, True)).toMap, bodyWOLets)
        constraints = constraints :+ Constraint(vcPrecondition, body, Or(postConditions), "wholebody")
        (bodyWOLets, body)
      // 'Normal' function R^n -> R
      case Some(post) =>
        val body = convertLetsToEquals(addResult(funDef.body.get))
        constraints = constraints :+ Constraint(vcPrecondition, body, post, "wholeBody")
        allFncCalls ++= functionCallsOf(post).map(invc => invc.funDef.id.toString)
        (body, body)
      // Auxiliary function, nothing to prove
      case None =>
        if (funDef.returnType == BooleanType) reporter.warning("Forgotten holds on invariant " + funDef.id + "?")
        val body = convertLetsToEquals(addResult(funDef.body.get))
        (body, body)
    }

    if (containsAssertion(bodyProcessed)) {
      val noiseRemover = new NoiseRemover
      val paths = collectPaths(bodyProcessed)
      for (path <- paths) {
        var i = 0
        while (i != -1) {
          val j = path.expression.indexWhere(e => containsAssertion(e), i)
          if (j != -1) {
            i = j + 1
            val pathToAssert = path.expression.take(j)
            path.expression(j) match {
              case Assertion(expr) =>
                constraints = constraints :+ Constraint(
                      And(vcPrecondition, path.condition), And(pathToAssert), expr, "assertion")
              case x =>
                reporter.warning("This was supposed to be an assertion: " + x)
            }
          } else { i = -1}
        }
      }
    }

    constraints = constraints.map(c => Constraint(c.pre, assertionRemover.transform(c.body), c.post, c.description))

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
                  constraints = constraints :+ Constraint(
                      And(vcPrecondition, path.condition), And(pathToFncCall), postcondition, "pre of call " + fncCall.toString)
                case None => ;
              }
            }
          } else { i = -1}
        }
      }
    }


    //println("all fncCalls: " + vc.allFncCalls)
    if (verbose) reporter.info("All constraints generated: ")
    if (verbose) reporter.info(constraints.mkString("\n -> ") )

    //vc.funcArgs = vc.funDef.args.map(v => Variable(v.id).setType(RealType))
    //vc.localVars = allLetDefinitions(funDef.body.get).map(letDef => Variable(letDef._1).setType(RealType))

    val vc = VerificationCondition(funDef, inputVariables, vcPrecondition, vcBody, allFncCalls, constraints)
    println("vc: " + vc)
    vc
  }

  // Has to run before we removed the lets!
  // Basically the first free expression that is not an if or a let is the result
  private def addResult(expr: Expr): Expr = expr match {
    case IfExpr(cond, then, elze) => IfExpr(cond, addResult(then), addResult(elze))
    case Let(binder, value, body) => Let(binder, value, addResult(body))
    case UMinus(_) | Plus(_, _) | Minus(_, _) | Times(_, _) | Division(_, _) | Sqrt(_) | FunctionInvocation(_, _) | Variable(_) =>
      Equals(ResultVariable(), expr)
    case Block(exprs, last) => Block(exprs, addResult(last))
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

    case Block(exprs, last) =>
      And(exprs :+ last)

    case _ => expr

  }


  def containsAssertion(expr : Expr) : Boolean = {
    def convert(t : Expr) : Boolean = t match {
      case f : Assertion => true
      case _ => false
    }
    def combine(c1 : Boolean, c2 : Boolean) : Boolean = c1 || c2
    def compute(t : Expr, c : Boolean) = t match {
      case f : Assertion => true
      case _ => c
    }
    treeCatamorphism(convert, combine, compute, expr)
  }

  class AssertionRemover extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case Assertion(expr) => True
      case _ =>
        super.rec(e, path)
    }
  }
}
