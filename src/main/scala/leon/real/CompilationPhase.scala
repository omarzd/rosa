/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import java.io.{PrintWriter, File}

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.ScalaPrinter


object CompilationPhase extends LeonPhase[Program,CompilationReport] {
  val name = "Real compilation"
  val description = "compilation of real programs"

  implicit val debugSection = utils.DebugSectionReals

  var reporter: Reporter = null
  private def debug(msg: String): Unit = {
    reporter.debug(msg)
  }

  override val definedOptions: Set[LeonOptionDef] = Set(
    LeonValueOptionDef("functions", "--functions=f1:f2", "Limit verification to f1, f2,..."),
    LeonFlagOptionDef("simulation", "--simulation", "Run a simulation instead of verification"),
    LeonFlagOptionDef("z3Only", "--z3Only", "Let Z3 loose on the full constraint - at your own risk."),
    LeonValueOptionDef("z3Timeout", "--z3Timeout=1000", "Timeout for Z3 in milliseconds."),
    LeonValueOptionDef("precision", "--precision=single", "Which precision to assume of the underlying"+
      "floating-point arithmetic: single, double, doubledouble, quaddouble or all (sorted from smallest)."),
    LeonFlagOptionDef("pathError", "--pathError", "Check also the path error (default is to not check)"),
    LeonFlagOptionDef("specGen", "--specGen", "Generate specs also for functions without postconditions")
  )

  def run(ctx: LeonContext)(program: Program): CompilationReport = {
    reporter = ctx.reporter
    reporter.info("Running Compilation phase")

    var fncNamesToAnalyse = Set[String]()
    var options = RealOptions()

    for (opt <- ctx.options) opt match {
      case LeonValueOption("functions", ListValue(fs)) => fncNamesToAnalyse = Set() ++ fs
      case LeonFlagOption("simulation", v) => options = options.copy(simulation = v)
      case LeonFlagOption("z3Only", v) => options = options.copy(z3Only = v)
      case LeonFlagOption("pathError", v) => options = options.copy(pathError = v)
      case LeonFlagOption("specGen", v) => options = options.copy(specGen = v)
      case LeonValueOption("z3Timeout", ListValue(tm)) => options = options.copy(z3Timeout = tm.head.toLong)
      case LeonValueOption("precision", ListValue(ps)) => options = options.copy(precision = ps.flatMap {
        case "single" => List(Float32)
        case "double" => List(Float64)
        case "doubledouble" => List(DoubleDouble)
        case "quaddouble" => List(QuadDouble)
        case "all" => List(FPPrecision(8), FPPrecision(16), FPPrecision(32), FPPrecision(64), Float32, Float64, DoubleDouble, QuadDouble)
        case x => List(FPPrecision(x.toInt))
      }.toList)
      case _ =>
    }

    //println("options: " + options)

    val fncsToAnalyse  =
      if(fncNamesToAnalyse.isEmpty) program.definedFunctions.filter(f =>
        !f.annotations.contains("proxy"))
      else {
        val toAnalyze = program.definedFunctions.filter(f => {
          !f.annotations.contains("proxy") && fncNamesToAnalyse.contains(f.id.name)})
        val notFound = fncNamesToAnalyse -- toAnalyze.map(fncDef => fncDef.id.name).toSet
        notFound.foreach(fn => reporter.error("Did not find function \"" + fn + "\" though it was marked for analysis."))
        toAnalyze
      }

    val (vcs, fncs) = Analyser.analyzeThis(fncsToAnalyse, options.precision, reporter)
    if (reporter.errorCount > 0) throw LeonFatalError(None)

    //println("functions sorted: " + vcs)
    //fncs.foreach(f => println(f.fncId))

    reporter.info("--- Analysis complete ---")
    reporter.info("")
    if (options.simulation) {
      val simulator = new Simulator(ctx, options, program, reporter, fncs)
      val prec = if (options.precision.size == 1) options.precision.head else Float64
      for(vc <- vcs) simulator.simulateThis(vc, prec)
      new CompilationReport(List(), prec)
    } else {
      val prover = new Prover(ctx, options, program, fncs)

      val (finalPrecision, success) = prover.check(vcs)
      if (success) {
        val codeGenerator = new CodeGenerator(reporter, ctx, options, program, finalPrecision, fncs)
        val newProgram = codeGenerator.specToCode(program.id, program.modules(0).id, vcs)
        val newProgramAsString = ScalaPrinter(newProgram)
        reporter.info("Generated program with %d lines.".format(newProgramAsString.lines.length))
        //reporter.info(newProgramAsString)

        val writer = new PrintWriter(new File("generated/" + newProgram.modules(0).id +".scala"))
        writer.write(newProgramAsString)
        writer.close()
      }
      else {// verification did not succeed for any precision
        reporter.warning("Could not find data type that works for all methods.")
      }

      new CompilationReport(vcs.sortWith((vc1, vc2) => vc1.fncId < vc2.fncId), finalPrecision)
    }

  }

}
