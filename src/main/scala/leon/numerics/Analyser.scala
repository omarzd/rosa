package leon
package numerics

import ceres.common._

import purescala.Trees._
import purescala.TreeOps
import purescala.Definitions._
import purescala.Common._

class Analyser(reporter: Reporter) {

  def analyzeThis(funDef: FunDef): VerificationCondition = {
    val vc = new VerificationCondition(funDef)
    funDef.precondition match {
      case Some(p) =>
        vc.inputRanges = Utils.getVariableBounds(p)
        vc.precondition = Some(p)
      case None =>
        vc.precondition = Some(BooleanLiteral(true))
    }

    funDef.postcondition match {
      case Some(p) =>
        if (isComplete(p)) vc.postcondition = Some(p)
        else vc.postcondition = Some(computePost(funDef.body.get, vc.inputRanges, vc.precondition.get))
      case None =>
        vc.postcondition = Some(computePost(funDef.body.get, vc.inputRanges, vc.precondition.get))
    }
    vc
  }

  // It is complete, if the result is bounded below and above and the noise is specified.
  private def isComplete(post: Expr): Boolean = {
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

  private def computePost(body: Expr, inputs: Map[Variable, RationalInterval], pre: Expr): Expr = {
    BooleanLiteral(true)
  }


}
