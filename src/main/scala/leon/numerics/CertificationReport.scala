package leon
package numerics

object CertificationReport {
  def emptyReport: CertificationReport = new CertificationReport(Nil)


  /*private val infoHeader: String = " |---------|\n" +
                                   "| Summary |-" + ("-" * 67) + "|\n" +
                                   "|_________|"
  */

  private val infoHeader: String = ("-" * 19) + ">" + ("*" * 20) + "\n" +
                                   (" " * 20) + "*     Summary     *\n" +
                                   (" " * 20) + ("*" * 20)

  //private val infoSep: String = "|" + ("_" * 78) + "|\n"

  private def infoLineVerbose(fc: VerificationCondition): String = {
    "\n%s \nwith R: %s\nw/o R:%s".format(
      fc.funDef.id.toString,
      formatOption(fc.fncConstraintWithRoundoff),
      formatOption(fc.fncConstraintRealArith))
  }

  private def infoLine(fc: VerificationCondition): String = {
    "\n%s \nwith R: %s\nw/o R:%s\nconstraints generated in: %s ms".format(
      fc.funDef.id.toString,
      fc.formulaStats(fc.fncConstraintWithRoundoff),
      fc.formulaStats(fc.fncConstraintRealArith),
      formatOption(fc.constraintGenTime))
  }


   private def formatOption[T](res: Option[T]): String = res match {
    case Some(xf) => xf.toString
    case None => "[?, ?]"
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
