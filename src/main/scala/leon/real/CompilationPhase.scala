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

    // Generate VCs (separate, but mark those that are for spec gen)

    // Verification
   
    new CompilationReport()
  }
}