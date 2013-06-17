package leon
package numerics

import ceres.common._

import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Definitions._
import purescala.Common._
import Utils._


class Analyser(reporter: Reporter) {

  val verbose = true

  // Currently the only constraint is the full function.
  def analyzeThis(funDef: FunDef): VerificationCondition = {
    reporter.info("")
    reporter.info("-----> Analysing function " + funDef.id.name + "...")

    val vc = new VerificationCondition(funDef)
    funDef.precondition match {
      case Some(p) =>
        val collector = new VariableCollector
        collector.transform(p)
        vc.inputs = collector.recordMap
        if (verbose) reporter.info("inputs: " + vc.inputs)
        vc.precondition = Some(p)
      case None =>
        vc.precondition = Some(BooleanLiteral(true))
    }

    // Preprocess body
    vc.body = Some(convertLetsToEquals(addResult(funDef.body.get)))

    // whole func constraint, must be first
    funDef.postcondition match {
      case Some(post) =>
        vc.allConstraints = List(Constraint(vc.precondition.get, vc.body.get, post))
      case None => ;
    }

// TODO: function calls, invariants

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

  private def convertLetsToEquals(expr: Expr): Expr = expr match {
    case IfExpr(cond, then, elze) =>
      IfExpr(cond, convertLetsToEquals(then), convertLetsToEquals(elze))

    case Let(binder, value, body) =>
      And(Equals(Variable(binder), convertLetsToEquals(value)), convertLetsToEquals(body))

    case _ => expr

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
