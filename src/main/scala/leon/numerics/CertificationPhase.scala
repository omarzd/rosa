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

  def generateVCs(reporter: Reporter, functions: Seq[FunDef]): List[VerificationCondition] = {
    var allVCs: Seq[VerificationCondition] = Seq.empty
    val analyser = new ConstraintGenerator(reporter)
    for(funDef <- functions) {
      if (funDef.body.isDefined) {
        reporter.info("")
        reporter.info("-----> Analysing function " + funDef.id.name + "...")
        val fc = new VerificationCondition(funDef)
        val start = System.currentTimeMillis
        fc.fncConstraintWR = Some(analyser.getConstraint(funDef, true))
        fc.fncConstraintRA = Some(analyser.getConstraint(funDef, false))
        val totalTime = (System.currentTimeMillis - start)
        fc.constraintGenTime = Some(totalTime)
        allVCs = allVCs :+ fc
      }
    }

    allVCs.toList
  }

  def checkVCs(reporter: Reporter, vcs: Seq[VerificationCondition],
    ctx: LeonContext, program: Program): CertificationReport = {

    val solver = new NumericSolver(ctx, program)
    val prover = new Prover(reporter, solver)
    //val tools = new Tools(reporter)

    for(vc <- vcs) {
      // TODO: if no postcondition to check do specs generation, i.e. QE

      prover.check(vc)

    }
    new VerificationReport(vcs)
  }

  def simulate(reporter: Reporter, functions: Seq[FunDef]): SimulationReport = {
    val simulator = new Simulator
    var results: List[SimulationResult] = List.empty
    for(funDef <- functions) {
      if (funDef.body.isDefined) {
        reporter.info("-----> Simulating function " + funDef.id.name + "...")
        var variableBounds = Utils.getVariableBounds(funDef.precondition.get) 
        results = results :+ simulator.simulate(funDef.id.name, funDef.body.get, variableBounds)
      }
    }
    new SimulationReport(results)
  }

  // No Reals should be left over
  // Add the correct runtime checks
  //def prepareFroCodeGeneration { }

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
