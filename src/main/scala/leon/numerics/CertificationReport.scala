package leon
package numerics

import ceres.common.Interval

import purescala.Common._
import purescala.TreeOps._
import purescala.Trees._

import Valid._
import Utils._

object CertificationReport {
  val infoSep    : String = "╟" + ("┄" * 83) + "╢"
  val infoFooter : String = "╚" + ("═" * 83) + "╝"
  val infoHeader : String = ". ┌─────────┐\n" +
                                    "╔═╡ Summary ╞" + ("═" * 71) + "╗\n" +
                                    "║ └─────────┘" + (" " * 71) + "║"

  def infoLineCnstr(c: Constraint): String = (c.status, c.model) match {
    case (Some(INVALID), Some(m)) =>
      "║      %-10s %-10s %10s        %-36s ║\n".format(
        c.numVariables,
        c.size,
        "INVALID", c.description
      ) +
      c.model.get.toSeq.map( x => "║ %-30s %-15s %-34s ║".format("", x._1, x._2)).mkString("\n")
    case (Some(x), _) =>
      "║      %-10s %-10s %10s        %-36s ║".format(
        c.numVariables,
        c.size,
        x.toString, c.description
      )
    case (None, _) => "║ %-30s %s %-30s ║".format("", " -- ", "")
  }


  def infoLine(vc: VerificationCondition): String = {
    val line = "║ %-30s %-10s %-10s %-28s ║".format(
      vc.funDef.id.toString,
      formatOption(vc.analysisTime)+"ms",
      formatOption(vc.verificationTime)+"ms",
      "") +
    vc.allConstraints.map(infoLineCnstr).mkString("\n", "\n", "\n")

    vc.simulationRange match {
      case Some(sr) =>
        line + "║ sim range: %-31s (%-20s) %-9s ║\n║ int range: %-31s %-32s║\n║ aa range: %-63s║\n".format(
          sr.toString, formatOption(vc.rndoff),"", formatOption(vc.intervalRange), "", formatOption(vc.affineRange)) + infoSep
      case None => line + infoSep
    }
  }


  private def formatStatus(status: Option[Valid], model: Option[Map[Identifier, Expr]]) = (status, model) match {
    case (Some(INVALID), Some(m)) => "(Invalid)\n  counterexample: " + m.toString
    case (Some(x), _) => "(" + x.toString + ")"
    case (None, _) => " -- "
  }

}

case class CertificationReport(val fcs: Seq[VerificationCondition]) {
  import CertificationReport._

  def summaryString: String =
    if(fcs.length >= 0) {
      infoHeader +
      fcs.map(infoLine).mkString("\n", "\n", "\n") +
      infoFooter
    } else {
      "Nothing to show."
    }
}
