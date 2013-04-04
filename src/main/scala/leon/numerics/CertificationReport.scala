package leon
package numerics

object CertificationReport {
  def emptyReport: CertificationReport = new CertificationReport(Nil)


  private val infoHeader: String = " |---------|\n" +
                                   "| Summary |-" + ("-" * 37) + "|\n" +
                                   "|_________|"

  private val infoSep: String = "|" + ("_" * 48) + "|\n"

  private def infoLine(vc: VerificationCondition): String = {
    "|%-25s  %-10s %-10s|".format(
      vc.funDef.id.toString,
      vc.status,
      vc.time)
  }
}

// TODO: look at Verification report and copy...
case class CertificationReport(val vcs: Seq[VerificationCondition]) {
  import CertificationReport._

  def summaryString: String = if(vcs.length >= 0) {
    infoHeader +
    vcs.map(infoLine).mkString("\n", "\n", "\n") +
    infoSep +
    "..."
  } else {
    "No verification conditions were analyzed."
  }
}
