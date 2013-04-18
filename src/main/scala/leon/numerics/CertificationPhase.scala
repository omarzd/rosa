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
  var simulation = false

  override val definedOptions: Set[LeonOptionDef] = Set(
    LeonValueOptionDef("functions", "--functions=f1:f2", "Limit verification to f1, f2,..."),
    LeonFlagOptionDef("simulation", "--simulation", "Run a simulation instead of proof")
  )

  /*
    Since we can have more than one VC for each function, we need to make sure
    that we cover everything, i.e. we don't show only a subpart.
  */
  def generateVerificationConditions(reporter: Reporter, program: Program,
    functionsToAnalyse: Set[String]):
    List[VerificationCondition] = {

    var allVCs: Seq[VerificationCondition] = Seq.empty
    val analysedFunctions: MutableSet[String] = MutableSet.empty

    val analyser = new Analyser(reporter)

    for(funDef <- program.definedFunctions.toList if (functionsToAnalyse.isEmpty || functionsToAnalyse.contains(funDef.id.name))) {
      analysedFunctions += funDef.id.name

      if (funDef.body.isDefined) {
        // for now, this only generate 1 VC per function, i.e. we accept only
        // simple mathematical expressions
        allVCs ++= analyser.generateVCs(funDef)
      }
    }

    val notFound = functionsToAnalyse -- analysedFunctions
    notFound.foreach(fn => reporter.error("Did not find function \"" + fn + "\" though it was marked for analysis."))

    allVCs.toList.sortWith((vc1, vc2) => vc1.funDef.id.name < vc2.funDef.id.name)
  }


  def checkVerificationConditions(reporter: Reporter, vcs: Seq[VerificationCondition],
    ctx: LeonContext, program: Program):
    CertificationReport = {

    val solver = new NumericSolver(ctx, program)
    val prover = new Prover(reporter, ctx, solver)
    val tools = new Tools(reporter)

    for(vc <- vcs) {
      if (simulation) tools.compare(vc)
      else prover.check(vc) 
    }
    new CertificationReport(vcs)
  }

  def run(ctx: LeonContext)(program: Program): CertificationReport = {
    val reporter = ctx.reporter

    var functionsToAnalyse = Set[String]()


    for (opt <- ctx.options) opt match {
      case LeonValueOption("functions", ListValue(fs)) =>
        functionsToAnalyse = Set() ++ fs
      
      case LeonFlagOption("simulation") =>
        simulation = true
      case _ =>
    }

    reporter.info("Running Certification phase")

    val vcs = generateVerificationConditions(reporter, program, functionsToAnalyse)
    reporter.info("Generated " + vcs.size + " verification conditions")
    checkVerificationConditions(reporter, vcs, ctx, program)
  }

}
