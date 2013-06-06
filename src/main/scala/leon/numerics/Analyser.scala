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

    funDef.postcondition match {
      case Some(post) =>
        vc.toCheck = vc.toCheck :+ Constraint(
          vc.precondition.get,
          convertLetsToEquals(funDef.body.get),
          post
        )
      case None => ;
    }
    
    vc.funcArgs = vc.funDef.args.map(v => Variable(v.id).setType(RealType))
    vc.localVars = allLetDefinitions(funDef.body.get).map(letDef => Variable(letDef._1).setType(RealType))
    println("func args: " + vc.funcArgs)
    println("local vars: " + vc.localVars)

    vc
  }

  private def convertLetsToEquals(expr: Expr): Expr = expr match {
    case IfExpr(cond, then, elze) =>
      IfExpr(cond, convertLetsToEquals(then), convertLetsToEquals(elze))

    case Let(binder, value, body) =>
      And(Equals(Variable(binder), value), convertLetsToEquals(body))
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
