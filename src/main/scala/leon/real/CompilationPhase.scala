/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import java.io.{PrintWriter, File}

import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.ScalaPrinter

import xlang.Trees._

import real.Trees._
import real.TreeOps._
import VCKind._


object CompilationPhase extends LeonPhase[Program,CompilationReport] {
  val name = "Real compilation"
  val description = "compilation of real programs"

  implicit val debugSection = DebugSectionVerification

  var verbose = true
  var reporter: Reporter = null

  override val definedOptions: Set[LeonOptionDef] = Set(
    LeonValueOptionDef("functions", "--functions=f1:f2", "Limit verification to f1, f2,..."),
    LeonFlagOptionDef("simulation", "--simulation", "Run a simulation instead of verification"),
    LeonFlagOptionDef("z3Only", "--z3Only", "Let Z3 loose on the full constraint - at your own risk."),
    LeonValueOptionDef("z3Timeout", "--z3Timeout=1000", "Timeout for Z3 in milliseconds."),
    LeonValueOptionDef("precision", "--precision=single", "Which precision to assume of the underlying"+
      "floating-point arithmetic: single, double, doubledouble, quaddouble or all (finds the best one)."),
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
      case LeonValueOption("precision", ListValue(ps)) => options = options.copy(precision = ps.head match {
        case "single" => List(Float32)
        case "double" => List(Float64)
        case "doubledouble" => List(DoubleDouble)
        case "quaddouble" => List(QuadDouble)
        // TODO: binary search?
        case "all" => List(FPPrecision(8), FPPrecision(16), FPPrecision(32), FPPrecision(64), Float32, Float64, DoubleDouble, QuadDouble)
        case x => List(FPPrecision(x.toInt))
      })
      case _ =>
    }

    println("options: " + options)

    val fncsToAnalyse  = 
      if(fncNamesToAnalyse.isEmpty) program.definedFunctions
      else {
        val toAnalyze = program.definedFunctions.filter(f => fncNamesToAnalyse.contains(f.id.name))
        val notFound = fncNamesToAnalyse -- toAnalyze.map(fncDef => fncDef.id.name).toSet
        notFound.foreach(fn => reporter.error("Did not find function \"" + fn + "\" though it was marked for analysis."))
        toAnalyze
      }
        
    val (vcs, fncs) = analyzeThis(fncsToAnalyse, options.precision)
    if (reporter.errorCount > 0) throw LeonFatalError()
    
    reporter.info("--- Analysis complete ---")
    reporter.info("")
    if (options.simulation) {
      val simulator = new Simulator(reporter)
      val prec = if (options.precision.size == 1) options.precision.head else Float64
      for(vc <- vcs) simulator.simulateThis(vc, prec)
      new CompilationReport(List(), prec)
    } else {
      val prover = new Prover(ctx, options, program, fncs, verbose)
      
      val (finalPrecision, success) = prover.check(vcs)
      if (success) {
        val codeGenerator = new CodeGenerator(reporter, ctx, options, program, finalPrecision)
        val newProgram = codeGenerator.specToCode(program.id, program.mainObject.id, vcs) 
        val newProgramAsString = ScalaPrinter(newProgram)
        reporter.info("Generated program with %d lines.".format(newProgramAsString.lines.length))
        //reporter.info(newProgramAsString)

        val writer = new PrintWriter(new File("generated/" + newProgram.mainObject.id +".scala"))
        writer.write(newProgramAsString)
        writer.close()
      }
      else {// verification did not succeed for any precision
        reporter.warning("Could not find data type that works for all methods.")
      }
      
      new CompilationReport(vcs.sortWith((vc1, vc2) => vc1.fncId < vc2.fncId), finalPrecision)
    }
    
  }

  

  private def analyzeThis(sortedFncs: Seq[FunDef], precisions: List[Precision]): (Seq[VerificationCondition], Map[FunDef, Fnc]) = {
    var vcs = Seq[VerificationCondition]()
    var fncs = Map[FunDef, Fnc]()
    
    for (funDef <- sortedFncs if (funDef.body.isDefined)) {
      reporter.info("Analysing fnc:  %s".format(funDef.id.name))
      if (verbose) reporter.debug("fnc body: " + funDef.body.get)
      
      funDef.precondition match {
        case Some(pre) =>
          val variables = VariablePool(pre)
          if (verbose) reporter.debug("parameter: " + variables)
          if (variables.hasValidInput(funDef.args)) {
            if (verbose) reporter.debug("precondition is acceptable")
            val allFncCalls = functionCallsOf(funDef.body.get).map(invc => invc.funDef.id.toString)
              //functionCallsOf(pre).map(invc => invc.funDef.id.toString) ++

            // Add default roundoff on inputs
            val precondition = And(pre, And(variables.inputsWithoutNoise.map(i => Roundoff(i))))
            if (verbose) reporter.debug("precondition: " + precondition)
            
            val (body, bodyWORes, postcondition) = funDef.postcondition match {
              //Option[(Identifier, Expr)]
              // TODO: invariants (got broken because of missing ResultVariable)
              /*case Some((ResultVariable()) =>
                val posts = getInvariantCondition(funDef.body.get)
                val bodyWOLets = convertLetsToEquals(funDef.body.get)
                val body = replace(posts.map(p => (p, True)).toMap, bodyWOLets)
                (body, body, Or(posts))*/

              // TODO: ResultVariable is a hack
              case Some((resId, postExpr)) =>
                (convertLetsToEquals(addResult(funDef.body.get)), convertLetsToEquals(funDef.body.get),
                  replace(Map(Variable(resId) -> ResultVariable()), postExpr))

              case None => // only want to generate specs
                (convertLetsToEquals(addResult(funDef.body.get)), convertLetsToEquals(funDef.body.get), True)
            }
            if (postcondition == True)
              vcs :+= new VerificationCondition(funDef, SpecGen, precondition, body, postcondition, allFncCalls, variables, precisions)
            else  
              vcs :+= new VerificationCondition(funDef, Postcondition, precondition, body, postcondition, allFncCalls, variables, precisions)

            // VCs for preconditions of fnc calls and assertions
            val assertionCollector = new AssertionCollector(funDef, precondition, variables, precisions)
            assertionCollector.transform(body)
            vcs ++= assertionCollector.vcs

            // for function inlining
            fncs += (funDef -> Fnc(precondition, bodyWORes, postcondition))
          } else {
            reporter.warning("Incomplete precondition! Skipping...")
          }
        case None =>
      }
    }
    (vcs.sortWith((vc1, vc2) => lt(vc1, vc2)), fncs)
  }

  private def lt(vc1: VerificationCondition, vc2: VerificationCondition): Boolean = {
    if (vc1.allFncCalls.isEmpty) true
    else if (vc2.allFncCalls.isEmpty) false
    else if (vc2.allFncCalls.contains(vc1.fncId)) true
    else if (vc1.allFncCalls.contains(vc2.fncId)) false
    else true
  }

  /*
  class AssertionRemover extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case Assertion(expr) => True
      case _ =>
        super.rec(e, path)
    }
  }*/
}