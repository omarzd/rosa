package leon
package numerics

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

object CertificationPhase extends LeonPhase[Program,CertificationReport] {
  val name = "Certification"
  val description = "Floating-point certification"

  /*
    Since we can have more than one VC for each function, we need to make sure
    that we cover everything, i.e. we don't show only a subpart.
  */
  def generateVerificationConditions(reporter: Reporter, program: Program):
    List[VerificationCondition] = {

    var allVCs: Seq[VerificationCondition] = Seq.empty

    val analyser = new Analyser(reporter)

    for(funDef <- program.definedFunctions.toList) {

      if (funDef.body.isDefined) {
        // for now, this only generate 1 VC per function, i.e. we accept only
        // simple mathematical expressions
        allVCs ++= analyser.generateVCs(funDef)
      }
    }
    allVCs.toList
  }


  def checkVerificationConditions(reporter: Reporter, vcs: Seq[VerificationCondition],
    ctx: LeonContext, program: Program):
    CertificationReport = {

    val solver = new NumericSolver(ctx, program)
    val prover = new Prover(reporter, ctx, solver)

    for(vc <- vcs) {
      prover.check(vc) 
    }
    new CertificationReport(vcs)
  }

  def run(ctx: LeonContext)(program: Program): CertificationReport = {
    val reporter = ctx.reporter

    reporter.info("Running Certification phase")

    val vcs = generateVerificationConditions(reporter, program)
    reporter.info("Generated " + vcs.size + " verification conditions")
    checkVerificationConditions(reporter, vcs, ctx, program)
  }

}
