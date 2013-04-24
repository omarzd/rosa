package leon
package numerics

object CertificationReport {
  def emptyReport: CertificationReport = new CertificationReport(Nil)


  private val infoHeader: String = " |---------|\n" +
                                   "| Summary |-" + ("-" * 67) + "|\n" +
                                   "|_________|"

  private val infoSep: String = "|" + ("_" * 78) + "|\n"

  private def infoLine(vc: VerificationCondition): String = {
    "|%-25s  %-10s %-10s %-29s\n    %-38s \n %-80s".format(
      vc.funDef.id.toString,
      vc.status,
      formatTime(vc.time),
      " ",
      formatResult(vc.res),
      vc.comments)
  }

  private def formatResult(res: Option[String]): String = res match {
    case Some(xf) => xf
    case None => "[?, ?]"
  }

  private def formatTime(time: Option[Double]): String = time match {
    case Some(xf) => xf.toString
    case None => " - "
  }

}

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
