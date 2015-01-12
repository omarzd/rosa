/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package real

import Valid._

// @param precision the precision that we were able to prove stuff with (or not)
class CompilationReport(val allVCs: Seq[VerificationCondition], precision: Precision) {
  val realVCs = allVCs.filter(vc => vc.kind != VCKind.SpecGen)
  val specGen = allVCs.filter(vc => vc.kind == VCKind.SpecGen)
  lazy val totalConditions : Int = realVCs.size

  lazy val totalTime : Double = realVCs.foldLeft(0.0d)((t,c) => t + c.time.getOrElse(0.0d) / 1000)

  lazy val totalValid : Int = realVCs.count(_.value(precision) == VALID)

  lazy val totalInvalid : Int = realVCs.count(_.value(precision) == INVALID)

  lazy val totalUnknown : Int = realVCs.count(_.value(precision) == UNKNOWN)

  def summaryString : String = if(totalConditions >= 0) {
    CompilationReport.infoHeader +
    realVCs.map(CompilationReport.infoLine(precision)).mkString("\n", "\n", "\n") +
    specGen.map(CompilationReport.timeLine).mkString("\n", "\n", "\n") +
    CompilationReport.infoSep +
    ("║ total: %-4d   valid: %-4d   invalid: %-4d   unknown %-4d " +
      (" " * 16) +
      " %7.3f ║\n").format(totalConditions, totalValid, totalInvalid, totalUnknown, totalTime) +
    ("║ precision: %-10s " + (" " * 59) + " ║\n").format(precision.toString) +
    CompilationReport.infoFooter
  } else {
    "No verification conditions were analyzed."
  }
}


object CompilationReport {
  def emptyReport : CompilationReport = new CompilationReport(Seq(), Float64)

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

  private def infoLine(precision: Precision)(vc : VerificationCondition) : String = {
    val timeStr = vc.time match {
      case Some(t) => "%-3.3f".format(t / 1000)
      case None => ""
    }

    "║ %-25s %-15s %3s %-8s %-10s %-7s %7s ║".format(
      fit(vc.funDef.id.toString, 25),
      vc.kind,
      "",
      vc.status(precision),
      "",
      "",
      timeStr)
  }

  private def timeLine(vc : VerificationCondition) : String = {
    val timeStr = vc.time match {
      case Some(t) => "%-3.3f".format(t / 1000)
      case None => ""
    }

    "║ %-25s %-47s %7s ║".format(
      fit(vc.funDef.id.toString, 25),
      "",
      timeStr)
  }
}
