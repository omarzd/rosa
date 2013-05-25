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

  def generateFunctionConstraints(reporter: Reporter, program: Program,
    functionsToAnalyse: Set[String]): List[FunctionConstraint] = {

    var allFCs: Seq[FunctionConstraint] = Seq.empty
    val analysedFunctions: MutableSet[String] = MutableSet.empty

    val analyser = new ConstraintGenerator(reporter)
    val sortedFncs =
      if(functionsToAnalyse.isEmpty) program.definedFunctions.toList.sortWith((f1, f2) => f1.id.name < f2.id.name)
      else program.definedFunctions.filter(f => functionsToAnalyse.contains(f.id.name)).sortWith(
        (f1, f2) => f1.id.name < f2.id.name)

    for(funDef <- sortedFncs) {
      analysedFunctions += funDef.id.name

      if (funDef.body.isDefined) {
        val fc = new FunctionConstraint(funDef)
        val start = System.currentTimeMillis
        fc.fncConstraintWithRoundoff = Some(analyser.getConstraint(funDef, true))
        fc.fncConstraintRealArith = Some(analyser.getConstraint(funDef, false))
        val totalTime = (System.currentTimeMillis - start)
        fc.constraintGenTime = Some(totalTime)
        allFCs = allFCs :+ fc
      }
    }

    val notFound = functionsToAnalyse -- analysedFunctions
    notFound.foreach(fn => reporter.error("Did not find function \"" + fn + "\" though it was marked for analysis."))

    allFCs.toList.sortWith((vc1, vc2) => vc1.funDef.id.name < vc2.funDef.id.name)
  }


  /*def checkVerificationConditions(reporter: Reporter, vcs: Seq[VerificationCondition],
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
  }*/

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

    val fcs = generateFunctionConstraints(reporter, program, functionsToAnalyse)
    //reporter.info("Generated " + vcs.size + " verification conditions")
    //checkVerificationConditions(reporter, vcs, ctx, program)
    new CertificationReport(fcs)
  }

}
