/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees._

class Prover(reporter: Reporter, options: RealOptions) {

  def check(vcs: Seq[VerificationCondition]) = {
    for (vc <- vcs) {

      val start = System.currentTimeMillis


      

      val end = System.currentTimeMillis
      vc.time = Some(end - start)
    }
  }

  def checkValid(app: Approximation): Option[Boolean] = {
    None
  }

}

case class Approximation(cnstrs: List[Expr])

class Approximator {

  def getApproximation(vc: VerificationCondition): Approximation = {
    Approximation(List(Implies(And(vc.pre, vc.body), vc.post)))
    // Step one: full constraint, i.e. translation from ArithF into the (1 + delta) stuff

    // Step two: approximate the floating-point constraints with XFloat
  }

}