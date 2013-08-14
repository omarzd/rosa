/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Definitions._

object CompilationPhase extends LeonPhase[Program,CompilationReport] {
  val name = "Certification"
  val description = "compilation of real programs"


  def run(ctx: LeonContext)(program: Program): CompilationReport = {
    val reporter = ctx.reporter
    reporter.info("Running Compilation phase")

    println("Program: ")
    println(program)

    /*
      Analysis
     */
    // extract range bounds from specs and replace by WithIn
    // Generate a map from real to actual variables, incl. the noises, roundoff etc. (previously Record and getVariables)




    /* 
      VC generation
     */
    // Generate VCs (separate, but mark those that are for spec gen)
    // If the postcondition mentions the actual values, generate float arithmetic trees of the expression of the least possible precision
    

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