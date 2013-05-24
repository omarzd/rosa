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

  private def infoLine(fc: FunctionConstraint): String = {
    "%s \n %s".format(fc.funDef.id.toString, fc.constraint)
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

case class CertificationReport(val fcs: Seq[FunctionConstraint]) {
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
