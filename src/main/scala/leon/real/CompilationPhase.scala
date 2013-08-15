/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Definitions._

import Precision._


object CompilationPhase extends LeonPhase[Program,CompilationReport] {
  val name = "Real compilation"
  val description = "compilation of real programs"

  var verbose = true

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
    val reporter = ctx.reporter
    reporter.info("Running Compilation phase")

    var functionsToAnalyse = Set[String]()
    val options = new RealOptions

    for (opt <- ctx.options) opt match {
      case LeonValueOption("functions", ListValue(fs)) => functionsToAnalyse = Set() ++ fs
      case LeonFlagOption("simulation") => options.simulation = true
      case LeonFlagOption("pathSensitive") => options.pathSensitive = true
      case LeonFlagOption("z3only") => options.z3Only = true
      case LeonValueOption("z3timeout", ListValue(tm)) => options.z3Timeout = tm.head.toLong
      case LeonValueOption("precision", ListValue(ps)) => options.precision = ps.toList.map(p => p match {
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
    if (verbose) println("real options: " + options.toString)

    // TODO: sorting by function calls
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

    if (verbose) println("functions to analyze: " + sortedFncs.map(f => f.id.name))

    
    /*
      Analysis
     */
    // extract range bounds from specs and replace by WithIn
    // Generate a map from real to actual variables, incl. the noises, roundoff etc. (previously Record and getVariables)

    
    if (reporter.errorCount > 0) throw LeonFatalError()


    /* 
      VC generation
     */
    // Generate VCs (separate, but mark those that are for spec gen)
    // If the postcondition mentions the actual values, generate float arithmetic trees of the expression of the least possible precision
    // this needs to handle the path-sensitivity and how methods are handled

    /*
      VC check
     */
    /*
      Then we need
      - evaluate the float arithmetic in xfloats
      - translate to Z3 (with all that (1 + delta) business) 
      - stand-alone fnc to approximate ideal and actual expressions
      - an algorithm to cycle through different approximations
    */

    // Spec generation. Ideally we search through what we have proven so far, and use that, 
    // or take this into account already at analysis phase   


    /* Wishlist:
      - real part has products (instead of the times trees) and the compiler is free to choose any order for the actual part
    
  
    */
    new CompilationReport()
  }
}