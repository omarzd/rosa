package leon
package numerics

object CertificationReport {
  def emptyReport: CertificationReport = new CertificationReport(Nil)


  private val infoHeader: String = " |---------|\n" +
                                   "| Summary |-" + ("-" * 64) + "|\n" +
                                   "|_________|"

  private val infoSep: String = "|" + ("_" * 75) + "|\n"

  private def infoLine(vc: VerificationCondition): String = {
    "|%-25s  %-10s %-10s %-26s|\n|    %-30s |".format(
      vc.funDef.id.toString,
      vc.status,
      vc.time,
      " ",
      formatResult(vc.res))
  }

  private def formatResult(res: Option[XFloat]): String = res match {
    case Some(xf) => xf.toString
    case None => "[?, ?]"
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
