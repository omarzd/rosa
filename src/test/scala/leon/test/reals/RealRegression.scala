/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package test
package real

import leon.real.{CompilationPhase,CompilationReport}

import java.io.File

class RealRegression extends LeonTestSuite {
  private var counter : Int = 0
  private def nextInt() : Int = {
    counter += 1
    counter
  }
  private case class Output(report : CompilationReport, reporter : Reporter)

  private def mkPipeline : Pipeline[List[String],CompilationReport] =
    leon.frontends.scalac.ExtractionPhase andThen leon.utils.SubtypingPhase andThen leon.real.CompilationPhase

  // for now one, but who knows
  val realLibraryFiles = filesInResourceDir(
    "regression/verification/real/library", _.endsWith(".scala"))

  private def mkTest(file : File, leonOptions : Seq[LeonOption], forError: Boolean)(block: Output=>Unit) = {
    val fullName = file.getPath()
    val start = fullName.indexOf("regression")

    val displayName = if(start != -1) {
      fullName.substring(start, fullName.length)
    } else {
      fullName
    }

    test("%3d: %s %s".format(nextInt(), displayName, leonOptions.mkString(" "))) {
      assert(file.exists && file.isFile && file.canRead,
             "Benchmark %s is not a readable file".format(displayName))


      val ctx = testContext.copy(
        settings = Settings(
          synthesis = false,
          xlang     = false,
          verify    = false,
          real = true
        ),
        options = leonOptions.toList,
        files = List(file) ++ realLibraryFiles
        //reporter = new SilentReporter
        //reporter = new DefaultReporter
      )

      val pipeline = mkPipeline

      if(forError) {
        intercept[LeonFatalError]{
          pipeline.run(ctx)(file.getPath :: Nil)
        }
      } else {

        val report = pipeline.run(ctx)(file.getPath :: Nil)

        block(Output(report, ctx.reporter))
      }
    }
  }

  private def mkIgnore(file: File) = {
    val fullName = file.getPath()
    val start = fullName.indexOf("regression")

    val displayName = if(start != -1) {
      fullName.substring(start, fullName.length)
    } else {
      fullName
    }
    ignore(displayName) {
      assert(true)
    }
  }

  private def forEachFileIn(cat : String, forError: Boolean = false)(block : Output=>Unit) {
    val fs = filesInResourceDir(
      "regression/verification/real/" + cat,
      _.endsWith(".scala"))

    for(f <- fs) {
      mkTest(f, List(LeonFlagOption("real", true)), forError)(block)
    }

    val ignoredFiles = filesInResourceDir(
      "regression/verification/real/" + cat,
      _.endsWith(".txt"))
    for(f <- ignoredFiles) {
      mkIgnore(f)
    }    
  }
  
  forEachFileIn("valid") { output =>
    val Output(report, reporter) = output
    assert(report.totalConditions === report.totalValid,
           "All verification conditions ("+report.totalConditions+") should be valid.")
    assert(reporter.errorCount === 0)
    assert(reporter.warningCount === 0)
  }

  forEachFileIn("unknown") { output =>
    val Output(report, reporter) = output
    assert(report.totalConditions === report.totalUnknown,
           "All verification conditions ("+report.totalConditions+") should be unknown.")
    assert(reporter.errorCount === 0) 
    assert(reporter.warningCount === 0)
  }
  //forEachFileIn("error", true) { output => () }

}
