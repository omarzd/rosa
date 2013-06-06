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
      "║      %-10s %-10s %10s %-43s ║\n".format(
        c.numVariables,
        c.size,
        "INVALID", ""
      ) + 
      c.model.get.toSeq.map( x => "║ %-30s %-15s %-34s ║".format("", x._1, x._2)).mkString("\n")
    case (Some(x), _) => 
      "║      %-10s %-10s %10s %-43s ║".format(
        c.numVariables,
        c.size,
        x.toString, ""
      )
    case (None, _) => "║ %-30s %s %-30s ║".format("", " -- ", "")
  }

  def infoLine(vc: VerificationCondition): String = {
    "║ %-30s %-10s %-10s %-28s ║".format(
      vc.funDef.id.toString,
      formatOption(vc.analysisTime)+"ms",
      formatOption(vc.verificationTime)+"ms",
      "") +
    vc.toCheck.map(infoLineCnstr).mkString("\n", "\n", "\n"+infoSep)
  }

  /*def infoLine(vc: VerificationCondition): String = {
    val constraints: String = vc.toCheck.foldLeft("")((str, c) =>
      str + "\n     %d      %d      %s".format(
        variablesOf(c.toProve).size, formulaSize(c.toProve), formatStatus(c.status, c.model)
      ))

    "\n%s \n%s\nanalysis time: %sms\nverif. time: %sms".format(
      vc.funDef.id.toString,
      constraints,
      formatOption(vc.analysisTime),
      formatOption(vc.verificationTime)
    )
  }*/


  /*def formatOption[T](res: Option[T]): String = res match {
    case Some(xf) => xf.toString
    case None => " -- "
  }*/

  private def formatStatus(status: Option[Valid], model: Option[Map[Identifier, Expr]]) = (status, model) match {
    case (Some(INVALID), Some(m)) => "(Invalid)\n  counterexample: " + m.toString
    case (Some(x), _) => "(" + x.toString + ")"
    case (None, _) => " -- "
  }
 
  /*private def formulaStats(expr: Option[Expr]): String = expr match {
    case Some(e) =>
      assert(variablesOf(e).size == allIdentifiers(e).size)
      "%d variables, formula size: %d".format(variablesOf(e).size, formulaSize(e))
    case None => " -- "
  }*/

}

abstract class CertificationReport {
  def summaryString: String
}

case class VerificationReport(val fcs: Seq[VerificationCondition]) extends CertificationReport {
  import CertificationReport._

  def summaryString: String =
    if(fcs.length >= 0) {
      infoHeader +
      fcs.map(infoLine).mkString("\n", "\n", "\n")
    } else {
      "Nothing to show."
    }
}

case class SimulationResult(funName: String, range: Interval, rndoff: Double) {
  override def toString: String = "%s: %s    (%s)".format(funName, range.toString, rndoff.toString)
}

case class SimulationReport(results: Seq[SimulationResult]) extends CertificationReport {
  import CertificationReport._

  def summaryString: String = {
    if(results.length >= 0) {
      infoHeader + results.mkString("\n")
    } else {
      "Nothing to show."
    }
  }
}
