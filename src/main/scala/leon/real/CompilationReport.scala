/* Copyright 2013 EPFL, Lausanne */

package leon
package real


class CompilationReport(vcs: Seq[VerificationCondition]) {

  lazy val totalConditions : Int = vcs.size

  lazy val totalTime : Double = vcs.foldLeft(0.0d)((t,c) => t + c.time.getOrElse(0.0d) / 1000)

  lazy val totalValid : Int = vcs.count(_.value == Some(true))

  lazy val totalInvalid : Int = vcs.count(_.value == Some(false))

  lazy val totalUnknown : Int = vcs.count(_.value == None)

  def summaryString : String = if(totalConditions >= 0) {
    CompilationReport.infoHeader +
    vcs.map(CompilationReport.infoLine).mkString("\n", "\n", "\n") +
    CompilationReport.infoSep +
    ("║ total: %-4d   valid: %-4d   invalid: %-4d   unknown %-4d " +
      (" " * 16) +
      " %7.3f ║\n").format(totalConditions, totalValid, totalInvalid, totalUnknown, totalTime) +
    CompilationReport.infoFooter
  } else {
    "No verification conditions were analyzed."
  }
}


object CompilationReport {
  def emptyReport : CompilationReport = new CompilationReport(Seq())

  private def fit(str : String, maxLength : Int) : String = {
    if(str.length <= maxLength) {
      str
    } else {
      str.substring(0, maxLength - 1) + "…"
    }
  }

  private val infoSep    : String = "╟" + ("┄" * 83) + "╢\n"
  private val infoFooter : String = "╚" + ("═" * 83) + "╝"
  private val infoHeader : String = ". ┌─────────┐\n" +
                                    "╔═╡ Summary ╞" + ("═" * 71) + "╗\n" +
                                    "║ └─────────┘" + (" " * 71) + "║"

  private def infoLine(vc : VerificationCondition) : String = {
    val timeStr = vc.time match {
      case Some(t) => "%-3.3f".format(t / 1000)
      case None => ""
    }

    "║ %-25s %-9s %9s %-8s %-10s %-7s %7s ║".format(
      fit(vc.funDef.id.toString, 25),
      vc.kind,
      "",
      vc.status,
      "",
      "",
      timeStr)
  }
}