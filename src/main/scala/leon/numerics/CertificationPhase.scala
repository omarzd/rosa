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
import SpecGenType._
import purescala.ScalaPrinter

import Utils._

import scala.collection.mutable.{Set => MutableSet}

object CertificationPhase extends LeonPhase[Program,CertificationReport] {
  val name = "Certification"
  val description = "Floating-point certification"
  var simulation = false
  var specgenType: SpecGenType = Simple
  var precision: Precision = Float64

  override val definedOptions: Set[LeonOptionDef] = Set(
    LeonValueOptionDef("functions", "--functions=f1:f2", "Limit verification to f1, f2,..."),
    LeonFlagOptionDef("simulation", "--simulation", "Run a simulation instead of verification"),
    LeonValueOptionDef("specgen", "--specgen=simple", "What kind of specs to generate: none, simple, pathsensitive"),
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
    val newProgram = codeGen.specToCode(program.id, program.mainObject.id, vcs, specgenType)
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
      case LeonValueOption("precision", ListValue(p)) => p.head match {
        case "double" => precision = Float64
        case "single" => precision = Float32
        case _=> reporter.warning("Ignoring unknown precision: " + p)
      }

      case LeonValueOption("specgen", ListValue(s)) => s.head match {
        case "simple" => specgenType = Simple
        case "pathsensitive" => specgenType = PathSensitive
        case "none" => specgenType = NoGen
        case _=> reporter.warning("Ignoring unknown specgen type: " + s)
      }
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

    val vcs = generateVCs(reporter, sortedFncs)
    if (reporter.errorCount > 0) throw LeonFatalError()
    val vcMap: Map[FunDef, VerificationCondition] = vcs.map { t => (t.funDef, t) }.toMap
    val sortedVCs = vcs.sortWith(
      (vc1, vc2) =>
        if (vc1.allFncCalls.size == 0) true
        else if (vc2.allFncCalls.size == 0) false
        else if (!vc1.allFncCalls.contains(vc2.id)) true
        else if (!vc2.allFncCalls.contains(vc1.id)) false
        else true//mutually recursive
      )
    println("vcs: " + vcs)
    println("sorted: " + sortedVCs)
    
    val prover = new Prover(reporter, ctx, program, vcMap, precision, specgenType)
    for(vc <- sortedVCs) prover.check(vc)

    if (simulation) {
      val simulator = new Simulator(reporter)
      for(vc <- vcs) simulator.simulateThis(vc, precision)
    }

    generateCode(reporter, program, vcs)
    new CertificationReport(vcs)
  }

}
