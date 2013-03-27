package leon
package numerics

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._

import TreeOps._

class Analyser(reporter: Reporter) {
  //class VerificationCondition(val inputs: Map[Expr, RationalInterval], val expr: Expr,
  //val output: RationalInterval, val absRoundoff: Rational) {


  def generateVCs(funDef: FunDef): Seq[VerificationCondition] = {
    var vcs: Seq[VerificationCondition] = Seq.empty
  
    val funName = funDef.id.name
    reporter.info("Analysing function " + funName + "...")
    
    val pre = funDef.precondition
    val post = funDef.postcondition
    val body = funDef.body.get

    //Need to check:
    //  - bounds are constraint
    //  - we can handle the body
    //  - we have something to prove
    if (post.isEmpty) {
      reporter.warning("no post, nothing to prove")
      Seq.empty
    } else if (pre.isEmpty){
      reporter.warning("no pre, unconstraint bounds")
      Seq.empty
    } else {
      val bounds = extractVariableBounds(pre.get)
      // TODO: check that all bounds have been defined
      if (bounds.isEmpty) {
        reporter.warning("unconstraint bounds")
        Seq.empty
      } else if(!isMathFunction(body)) {
        reporter.warning("function we cannot handle")
        Seq.empty
      } else {
        // everything seems to be fine
        val (outputRange, rndoff) = getGoal(post.get)
        if (outputRange.isEmpty && rndoff.isEmpty) {
          reporter.warning("nothing to prove")
          Seq.empty
        } else {
          // everything seems to be fine

          Seq(VerificationCondition(funDef, bounds, body, outputRange, rndoff))
        }
      }
    }
  }


}
