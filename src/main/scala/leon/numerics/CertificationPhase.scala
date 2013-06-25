package leon
package numerics

import java.io._

import ceres.common.Interval

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import Precision._
import purescala.ScalaPrinter

import Utils._

import scala.collection.mutable.{Set => MutableSet}

object CertificationPhase extends LeonPhase[Program,CertificationReport] {
  val name = "Certification"
  val description = "Floating-point certification"
  var simulation = false
  var specgen = true
  var precision: Precision = Float64

  override val definedOptions: Set[LeonOptionDef] = Set(
    LeonValueOptionDef("functions", "--functions=f1:f2", "Limit verification to f1, f2,..."),
    LeonFlagOptionDef("simulation", "--simulation", "Run a simulation instead of verification"),
    LeonFlagOptionDef("specgen", "--specgen", "Generate specifications in addition to verification."),
    LeonValueOptionDef("precision", "--precision=double", "Which precision to assume of the underlying floating-point arithmetic: single, double.")
  )


  def generateVCs(reporter: Reporter, functions: Seq[FunDef]): Seq[VerificationCondition] = {
    var allVCs: Seq[VerificationCondition] = Seq.empty
    val analyser = new Analyser(reporter)
    for(funDef <- functions if (funDef.body.isDefined)) {
      // TODO: why does the function body have to be defined?! We could also have functions that only function as API (e.g. closed source).
      allVCs = allVCs :+ analyser.analyzeThis(funDef)
    }
    allVCs
  }


  // TODO: add the correct runtime checks
  def generateCode(reporter: Reporter, program: Program, vcs: Seq[VerificationCondition]) = {
    val codeGen = new CodeGeneration(reporter, Float64)
    val newProgram = codeGen.specToCode(program.id, program.mainObject.id, vcs, specgen)
    val newProgramAsString = ScalaPrinter(newProgram)
    reporter.info("Generated program with %d lines.".format(newProgramAsString.lines.length))
    //reporter.info(newProgramAsString)

    val writer = new PrintWriter(new File("generated/" + newProgram.mainObject.id +".scala"))
    writer.write(newProgramAsString)
    writer.close()
  }


  def run(ctx: LeonContext)(program: Program): CertificationReport = {
    val reporter = ctx.reporter
    var functionsToAnalyse = Set[String]()
    reporter.info("Running Certification phase")

    for (opt <- ctx.options) opt match {
      case LeonValueOption("functions", ListValue(fs)) => functionsToAnalyse = Set() ++ fs
      case LeonFlagOption("simulation") => simulation = true
      case LeonFlagOption("specgen") => specgen = true
      case LeonValueOption("precision", ListValue(p)) =>
        if (p.head == "double") precision = Float64
        else if (p.head == "single") precision = Float32
        else reporter.warning("Ignoring unknown precision: " + p)
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

    // TODO: fail in some reasonable way if neither roundoff nor noise is specified
    // TODO: make specgen possible to disable
    val vcs = generateVCs(reporter, sortedFncs)

    if (reporter.errorCount > 0) {
      throw LeonFatalError()
    }

    val vcMap: Map[FunDef, VerificationCondition] = vcs.map { t => (t.funDef, t) }.toMap

    val prover = new Prover(reporter, ctx, program, vcMap, precision)
    for(vc <- vcs) prover.check(vc)

    if (simulation) {
      val simulator = new Simulator(reporter)
      for(vc <- vcs) simulator.simulateThis(vc, precision)
    }

    if (specgen) {
      val specgen = new SpecGen(reporter, prover)
      for(vc <- vcs) specgen.generateSpec(vc)
    }

    generateCode(reporter, program, vcs)
    new CertificationReport(vcs)



  }

}
