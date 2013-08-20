/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._

import xlang.Trees._

import real.Trees._
import real.TreeOps._
import real.ArithmeticOps._

import Precision._
import VCKind._


object CompilationPhase extends LeonPhase[Program,CompilationReport] {
  val name = "Real compilation"
  val description = "compilation of real programs"

  var verbose = true
  var reporter: Reporter = null

  override val definedOptions: Set[LeonOptionDef] = Set(
    LeonValueOptionDef("functions", "--functions=f1:f2", "Limit verification to f1, f2,..."),
    LeonFlagOptionDef("simulation", "--simulation", "Run a simulation instead of verification"),
    LeonFlagOptionDef("pathSensitive", "--pathSensitive", "Do a path sensitive analysis."),
    LeonFlagOptionDef("z3only", "--z3only", "Let Z3 loose on the full constraint - at your own risk."),
    LeonValueOptionDef("z3timeout", "--z3timeout=1000", "Timeout for Z3 in milliseconds."),
    LeonValueOptionDef("precision", "--precision=single:double", "Which precision to assume of the underlying"+
      "floating-point arithmetic: single, double, doubledouble, quaddouble."),
    LeonFlagOptionDef("nospecgen", "--nospecgen", "Don't generate specs.")
  )


  def run(ctx: LeonContext)(program: Program): CompilationReport = { 
    reporter = ctx.reporter
    reporter.info("Running Compilation phase")

    var fncNamesToAnalyse = Set[String]()
    val options = new RealOptions

    for (opt <- ctx.options) opt match {
      case LeonValueOption("functions", ListValue(fs)) => fncNamesToAnalyse = Set() ++ fs
      case LeonFlagOption("simulation") => options.simulation = true
      case LeonFlagOption("pathSensitive") => options.pathSensitive = true
      case LeonFlagOption("z3only") => options.z3Only = true
      case LeonValueOption("z3timeout", ListValue(tm)) => options.z3Timeout = tm.head.toLong
      case LeonValueOption("precision", ListValue(ps)) => options.precisions = ps.toList.map(p => p match {
        case "single" => Float32
        case "double" => Float64
        case "doubledouble" => DoubleDouble
        case "quaddouble" => QuadDouble
        case _=>
          reporter.warning("Unknown precision: " + p)
          Float64
      })
      case LeonFlagOption("nospecgen") => options.specGen = false
      case _ =>
    }
    
    val fncsToAnalyse  = 
      if(fncNamesToAnalyse.isEmpty) program.definedFunctions
      else {
        val toAnalyze = program.definedFunctions.filter(f => fncNamesToAnalyse.contains(f.id.name))
        val notFound = fncNamesToAnalyse -- toAnalyze.map(fncDef => fncDef.id.name).toSet
        notFound.foreach(fn => reporter.error("Did not find function \"" + fn + "\" though it was marked for analysis."))
        toAnalyze
      }
        
    val vcs = analyzeThis(fncsToAnalyse).sortWith((vc1, vc2) => lt(vc1, vc2))
    if (reporter.errorCount > 0) throw LeonFatalError()
    
    val prover = new Prover(ctx, options, program)
    prover.check(vcs)
    
    // Spec generation. Ideally we search through what we have proven so far, and use that, 
    // or take this into account already at analysis phase   


    /* Wishlist:
      - real part has products (instead of the times trees) and the compiler is free to choose any order for the actual part
    
  
    */
    // TODO sortWith((f1, f2) => f1.id.name < f2.id.name)
    new CompilationReport(vcs)

    // TODO: simulation
  }

  private def analyzeThis(sortedFncs: Seq[FunDef]): Seq[VerificationCondition] = {
    var vcs: Seq[VerificationCondition] = Seq.empty
    
    for (funDef <- sortedFncs if (funDef.body.isDefined)) {
      reporter.info("Analysing fnc  ==== %s ====".format(funDef.id.name))
      println(funDef.body.get)
      
      funDef.precondition match {
        case Some(precondition) =>
          val variables = VariablePool(precondition)
          println("parameters: " + variables)
          // TODO: fix this (result variable messing this up)
          //if (variables.isValid(funDef.args)) {
            println("prec. is complete, continuing")

            println("pre: " + precondition)
            val allFncCalls = functionCallsOf(precondition).map(invc => invc.funDef.id.toString) ++
              functionCallsOf(funDef.body.get).map(invc => invc.funDef.id.toString)

            val (fncBody, postcondition) = funDef.postcondition match {
              case Some(ResultVariable()) =>
                val posts = getInvariantCondition(funDef.body.get)
                val bodyWOLets = convertLetsToEquals(funDef.body.get)
                val body = replace(posts.map(p => (p, True)).toMap, bodyWOLets)
                (body, Or(posts))
              case Some(p) => (convertLetsToEquals(addResult(funDef.body.get)), p)

              case None => (convertLetsToEquals(addResult(funDef.body.get)), BooleanLiteral(true))
            }

            println("\nfncBody: " + fncBody)
            println("\npost: " + postcondition)

            println("\n body real : " + fncBody)
            println("\n body float: " + idealToActual(fncBody, variables))

            // add floating-point "track"
            val body = And(fncBody, idealToActual(fncBody, variables))

            // add all local variables to the variable store
            // TODO: does not work with blocks (xlang extension)
            variables.add(variablesOf(fncBody))
            println("all variables: " + variables)


            vcs :+= new VerificationCondition(funDef, Postcondition, precondition, body, postcondition, allFncCalls, variables)
            
            

            // TODO: vcs from assertions
            // TODO: vcs checking precondition of function calls

          //} else {
          //  reporter.warning("Incomplete precondition! Skipping...")
          //}
        case None =>
      }
    }
    vcs
  }

  private def lt(vc1: VerificationCondition, vc2: VerificationCondition): Boolean = {
    if (vc1.allFncCalls.isEmpty) true
    else if (vc2.allFncCalls.isEmpty) false
    else if (vc2.allFncCalls.contains(vc1.id)) true
    else if (vc1.allFncCalls.contains(vc2.id)) false
    else true
  }

}

