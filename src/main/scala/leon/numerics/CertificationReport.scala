package leon
package numerics

import purescala.TreeOps._
import purescala.Trees._

import Valid._

object CertificationReport {
  def emptyReport: CertificationReport = new CertificationReport(Nil)


  private val infoHeader: String = ".\n" + (" " * 19) + ">     Summary     <\n"

  private def infoLineVerbose(fc: VerificationCondition): String = {
    "\n%s \nwith R: %s\nw/o R:%s".format(
      fc.funDef.id.toString,
      formatOption(fc.fncConstraintWR),
      formatOption(fc.fncConstraintRA))
  }

  private def infoLine(fc: VerificationCondition): String = {
    "\n%s \nwith R: %s  %s\nw/o R:%s  %s\nconstraints generated in: %s ms".format(
      fc.funDef.id.toString,
      formulaStats(fc.fncConstraintWR),
      formatStatus(fc.statusWR, fc.modelWR),
      formulaStats(fc.fncConstraintRA),
      formatStatus(fc.statusRA, fc.modelWR),
      formatOption(fc.constraintGenTime))
  }


  private def formatOption[T](res: Option[T]): String = res match {
    case Some(xf) => xf.toString
    case None => " -- "
  }

  private def formatStatus(status: Option[Valid], model: Option[z3.scala.Z3Model]) = (status, model) match {
    case (Some(INVALID), Some(m)) => "(Invalid)\n  counterexample: " + m.toString
    case (Some(x), _) => "(" + x.toString + ")"
    case (None, _) => " -- "
  }
 
  private def formulaStats(expr: Option[Expr]): String = expr match {
    case Some(e) =>
      assert(variablesOf(e).size == allIdentifiers(e).size)
      "%d variables, formula size: %d".format(variablesOf(e).size, formulaSize(e))
    case None => " -- "
  }

}

case class CertificationReport(val fcs: Seq[VerificationCondition]) {
  import CertificationReport._

  def summaryString: String =
    if(fcs.length >= 0) {
    infoHeader +
    fcs.map(infoLine).mkString("\n", "\n", "\n") +
    "..."
  } else {
    "Nothing to show."
  }
}
