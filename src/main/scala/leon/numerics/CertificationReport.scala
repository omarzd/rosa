package leon
package numerics

object CertificationReport {
  def emptyReport: CertificationReport = new CertificationReport(Nil)

}

// TODO: look at Verification report and copy...
case class CertificationReport(val vcs: Seq[VerificationCondition]) {

  def summaryString: String = "CertificationReport to come..."
}
