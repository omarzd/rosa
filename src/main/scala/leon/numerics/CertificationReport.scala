package leon
package numerics

object CertificationReport {
  def emptyReport: CertificationReport = new CertificationReport(Nil)


  private val infoHeader: String = " |---------|\n" +
                                   "| Summary |-" + ("-" * 67) + "|\n" +
                                   "|_________|"

  private val infoSep: String = "|" + ("_" * 78) + "|\n"

  private def infoLine(vc: VerificationCondition): String = {
    "|%-25s  %-10s %-10s %-29s|\n|    %-33s |".format(
      vc.funDef.id.toString,
      vc.status,
      vc.time,
      " ",
      formatResult(vc.res))
  }

  private def formatResult(res: Option[String]): String = res match {
    case Some(xf) => xf
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
