package leon
package numerics

import ceres.common.Interval

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

import scala.collection.mutable.{Set => MutableSet}

object CertificationPhase extends LeonPhase[Program,CertificationReport] {
  val name = "Certification"
  val description = "Floating-point certification"

  override val definedOptions: Set[LeonOptionDef] = Set(
    LeonValueOptionDef("functions", "--functions=f1:f2", "Limit verification to f1, f2,..."),
    LeonFlagOptionDef("simulation", "--simulation", "Run a simulation instead of verification")
  )

  // Construct implications to prove
  def generateVCs(reporter: Reporter, functions: Seq[FunDef]): List[VerificationCondition] = {
    var allVCs: Seq[VerificationCondition] = Seq.empty
    val analyser = new Analyser(reporter)
    for(funDef <- functions if (funDef.body.isDefined)) {
      // TODO: why does the function body have to be defined?! We could also have functions that only function as API (e.g. closed source).

      allVCs = allVCs :+ analyser.analyzeThis(funDef)
  }

    allVCs.toList
  }

  // Only here should we do any kind of solving/computing
  def checkVCs(reporter: Reporter, vcs: Seq[VerificationCondition],
    ctx: LeonContext, program: Program): CertificationReport = {

    val prover = new Prover(reporter, ctx, program)
    //val tools = new Tools(reporter)

    for(vc <- vcs) {
      // TODO: if no postcondition to check do specs generation
      prover.check(vc)

    }
    new VerificationReport(vcs)
  }

  // TODO: Add eval with intervals and smartfloats
  def simulate(reporter: Reporter, functions: Seq[FunDef]): SimulationReport = {
    val simulator = new Simulator
    var results: List[SimulationResult] = List.empty
    for(funDef <- functions if (funDef.body.isDefined)) {
      reporter.info("-----> Simulating function " + funDef.id.name + "...")
      var variableBounds = Utils.getVariableBounds(funDef.precondition.get) 
      results = results :+ simulator.simulate(funDef.id.name, funDef.body.get, variableBounds)
    }
    new SimulationReport(results)
  }

  // No Reals should be left over
  // Add the correct runtime checks
  //def prepareFroCodeGeneration { }

  // TODO: Code generation
  def run(ctx: LeonContext)(program: Program): CertificationReport = {
    val reporter = ctx.reporter

    var functionsToAnalyse = Set[String]()
    var simulation = false

    for (opt <- ctx.options) opt match {
      case LeonValueOption("functions", ListValue(fs)) =>
        functionsToAnalyse = Set() ++ fs

      case LeonFlagOption("simulation") =>
        simulation = true
      case _ =>
    }

    val sortedFncs =
      if(functionsToAnalyse.isEmpty)
        program.definedFunctions.toList.sortWith((f1, f2) => f1.id.name < f2.id.name)
      else {
        val toAnalyze = program.definedFunctions.filter(
          f => functionsToAnalyse.contains(f.id.name)).sortWith(
          (f1, f2) => f1.id.name < f2.id.name)
        val notFound = functionsToAnalyse -- toAnalyze.map(fncDef => fncDef.id.name).toSet
        notFound.foreach(fn => reporter.error("Did not find function \"" + fn + "\" though it was marked for analysis."))
        toAnalyze
      }

    if (simulation) {
      simulate(reporter, sortedFncs)
    } else {
      reporter.info("Running Certification phase")
      val vcs = generateVCs(reporter, sortedFncs)
      checkVCs(reporter, vcs, ctx, program)
    }
  }

}
