package leon
package numerics

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

import leon.verification.VerificationReport

object CertificationPhase extends LeonPhase[Program,VerificationReport] {
  val name = "Certification"
  val description = "Floating-point certification"


  /*override val definedOptions: Set[LeonOptionDef] = Set(

  )*/

  //def generateVerificationConditions

  def run(ctx: LeonContext)(program: Program): VerificationReport = {


    VerificationReport.emptyReport
  }
  
}
