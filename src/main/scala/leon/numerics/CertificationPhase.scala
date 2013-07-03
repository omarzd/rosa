package leon
package numerics

import java.io._

import ceres.common.Interval

import z3.Z3Wrapper

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
  var specgen: Boolean = true
  var precision: Precision = Float64
  // default: try 'em all
  var precisionsToTry: List[Precision] = List(Float32, Float64, DoubleDouble, QuadDouble)

  // TODO: flag to switch off Z3 only versions, if Z3 hangs
  override val definedOptions: Set[LeonOptionDef] = Set(
    LeonValueOptionDef("functions", "--functions=f1:f2", "Limit verification to f1, f2,..."),
    LeonFlagOptionDef("simulation", "--simulation", "Run a simulation instead of verification"),
    LeonFlagOptionDef("nospecgen", "--nospecgen", "Don't generate specs."),
    LeonValueOptionDef("precision", "--precision=single:double", "Which precision to assume of the underlying floating-point arithmetic: single, double, doubledouble, quaddouble.")
  )


  def generateVCs(reporter: Reporter, functions: Seq[FunDef]): Seq[VerificationCondition] = {
    var allVCs: Seq[VerificationCondition] = Seq.empty
    val analyser = new Analyser(reporter)
    for(funDef <- functions if (funDef.body.isDefined)) {
      allVCs = allVCs :+ analyser.analyzeThis(funDef)
    }
    allVCs
  }


  def generateCode(reporter: Reporter, program: Program, vcs: Seq[VerificationCondition]) = {
    val codeGen = new CodeGeneration(reporter, precision)
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
    reporter.info("Z3 version: " + Z3Wrapper.z3VersionString)

    for (opt <- ctx.options) opt match {
      case LeonValueOption("functions", ListValue(fs)) => functionsToAnalyse = Set() ++ fs
      case LeonFlagOption("simulation") => simulation = true
      case LeonValueOption("precision", ListValue(ps)) => precisionsToTry = ps.toList.map(p => p match {
        case "single" => Float32
        case "double" => Float64
        case "doubledouble" => DoubleDouble
        case "quaddouble" => QuadDouble
        case _=>
          reporter.warning("Unknown precision: " + p)
          Float64
      })

      case LeonFlagOption("nospecgen") => specgen = false
      case _ =>
    }

    println("precisionsToTry: " + precisionsToTry)

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
    val sortedVCs = vcs.sortWith(
      (vc1, vc2) => // TODO: is this finally a stable sort?!
        !vc1.allFncCalls.contains(vc2.id)
        //if (vc1.allFncCalls.contains(vc2.id)) false
        //else vc1.id < vc2.id
      )



    println(sortedVCs)

    var currentVCs = sortedVCs
    println(currentVCs.forall(vc => vc.proven))
    while (!currentVCs.forall(vc => vc.proven) && !precisionsToTry.isEmpty) {
      precision = precisionsToTry.head
      reporter.info("Verification with precision: " + precision)
      var vcMap: Map[FunDef, VerificationCondition] = Map.empty //vcs.map { t => (t.funDef, t) }.toMap
      val prover = new Prover(reporter, ctx, program, precision, specgen)
      for (vc <- sortedVCs) {
        val checkedVC = prover.check(vc, vcMap)
        vcMap = vcMap + (checkedVC.funDef -> checkedVC)
      }
      //currentVCs = sortedVCs.map( vc => prover.check(vc) )
      currentVCs = vcMap.values.toSeq
      precisionsToTry = precisionsToTry.tail
      println("allProven: " + currentVCs.forall(vc => vc.proven))
    }

    if (simulation) {
      val simulator = new Simulator(reporter)
      for(vc <- vcs) simulator.simulateThis(vc, precision)
    }

    val sortedForCodeGen = currentVCs.sortWith((f1, f2) => f1.id < f2.id)
    generateCode(reporter, program, sortedForCodeGen)
    new CertificationReport(sortedForCodeGen)
  }

}
