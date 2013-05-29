package leon
package numerics

import ceres.common.Interval

import purescala.TreeOps._
import purescala.Trees._

import Valid._

object CertificationReport {

  val infoHeader: String = ".\n" + (" " * 19) + ">     Summary     <\n"

  def infoLineVerbose(fc: VerificationCondition): String = {
    "\n%s \nwith R: %s\nw/o R:%s".format(
      fc.funDef.id.toString,
      formatOption(fc.fncConstraintWR),
      formatOption(fc.fncConstraintRA))
  }

  def infoLine(fc: VerificationCondition): String = {
    "\n%s \nwith R: %s  %s\nw/o R:%s  %s\nconstraints generated in: %s ms".format(
      fc.funDef.id.toString,
      formulaStats(fc.fncConstraintWR),
      formatStatus(fc.statusWR._1, fc.statusWR._2),
      formulaStats(fc.fncConstraintRA),
      formatStatus(fc.statusRA._1, fc.statusRA._2),
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
