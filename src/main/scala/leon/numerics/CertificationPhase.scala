package leon
package numerics

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

import scala.collection.mutable.{Set => MutableSet}

object CertificationPhase extends LeonPhase[Program,CertificationReport] {
  val name = "Certification"
  val description = "Floating-point certification"
  //var simulation = false

  override val definedOptions: Set[LeonOptionDef] = Set(
    LeonValueOptionDef("functions", "--functions=f1:f2", "Limit verification to f1, f2,...")
    //LeonFlagOptionDef("simulation", "--simulation", "Run a simulation instead of proof")
  )

  def generateVCs(reporter: Reporter, program: Program,
    functionsToAnalyse: Set[String]): List[VerificationCondition] = {

    var allVCs: Seq[VerificationCondition] = Seq.empty
    val analysedFunctions: MutableSet[String] = MutableSet.empty

    val analyser = new ConstraintGenerator(reporter)
    val sortedFncs =
      if(functionsToAnalyse.isEmpty) program.definedFunctions.toList.sortWith((f1, f2) => f1.id.name < f2.id.name)
      else program.definedFunctions.filter(f => functionsToAnalyse.contains(f.id.name)).sortWith(
        (f1, f2) => f1.id.name < f2.id.name)

    for(funDef <- sortedFncs) {
      analysedFunctions += funDef.id.name

      if (funDef.body.isDefined) {
        val fc = new VerificationCondition(funDef)
        val start = System.currentTimeMillis
        fc.fncConstraintWR = Some(analyser.getConstraint(funDef, true))
        fc.fncConstraintRA = Some(analyser.getConstraint(funDef, false))
        val totalTime = (System.currentTimeMillis - start)
        fc.constraintGenTime = Some(totalTime)
        allVCs = allVCs :+ fc
      }
    }

    val notFound = functionsToAnalyse -- analysedFunctions
    notFound.foreach(fn => reporter.error("Did not find function \"" + fn + "\" though it was marked for analysis."))

    allVCs.toList
  }

  def checkVCs(reporter: Reporter, vcs: Seq[VerificationCondition],
    ctx: LeonContext, program: Program):
    CertificationReport = {

    val solver = new NumericSolver(ctx, program)
    val prover = new Prover(reporter, solver)
    //val tools = new Tools(reporter)

    for(vc <- vcs) {
      //if (simulation) tools.compare(vc) else prover.check(vc)

      prover.check(vc)
 /*     reporter.info("checking VC of " + vc.funDef.id.name)
      val validWithRndoff = solver.checkValid(vc.fncConstraintWithRoundoff.get)
      val validRealArith = solver.checkValid(vc.fncConstraintRealArith.get)
      reporter.info("valid with roundoff: " + validWithRndoff)
      reporter.info("valid real arithm: " + validRealArith)
  */
    }
    new CertificationReport(vcs)
  }

  def run(ctx: LeonContext)(program: Program): CertificationReport = {
    val reporter = ctx.reporter

    var functionsToAnalyse = Set[String]()


    for (opt <- ctx.options) opt match {
      case LeonValueOption("functions", ListValue(fs)) =>
        functionsToAnalyse = Set() ++ fs

      //case LeonFlagOption("simulation") =>
      //  simulation = true
      case _ =>
    }

    reporter.info("Running Certification phase")

    val vcs = generateVCs(reporter, program, functionsToAnalyse)
    //reporter.info("Generated " + vcs.size + " verification conditions")
    checkVCs(reporter, vcs, ctx, program)
    //new CertificationReport(fcs)
  }

}
