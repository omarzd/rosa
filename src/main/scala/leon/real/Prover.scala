/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import purescala.Definitions._
import purescala.TreeOps._

import Precision._
import Sat._

class Prover(ctx: LeonContext, options: RealOptions, prog: Program) {
  val reporter = ctx.reporter
  val solver = new RealSolver(ctx, prog, options.z3Timeout)
  //val approx = new Approximator(reporter, solver, options)

  def check(vcs: Seq[VerificationCondition]) = {
    for (vc <- vcs) {
      reporter.info("Verification condition (%s) ==== %s ====".format(vc.kind, vc.id))
      reporter.info("Trying with approximation")
      val start = System.currentTimeMillis

      val currentApprox = getApproximation(vc)
      reporter.info("  - " + currentApprox.name)
      println(currentApprox.cnstrs)
      checkValid(currentApprox, vc.variables) match {
        case Some(true) => reporter.info("==== VALID ====")
        case Some(false) => reporter.info("---- Unknown ----")
        case None => reporter.info("---- Unknown ----")
      }
      

      val end = System.currentTimeMillis
      vc.time = Some(end - start)
    }
  }

  def checkValid(app: Approximation, variables: VariablePool): Option[Boolean] = {

    val transformer = new LeonToZ3Transformer(variables)
    // FIXME: precision!
    val z3constraint = transformer.getZ3Expr(app.cnstrs.head, options.defaultPrecision)
    println("\n z3constraint: " + z3constraint)

    // FIXME: delta constraints are missing

    // TODO: arithmetic simplification

    // TODO: probably have to also replace ResultVariable and FResVariable

    // TODO: if (reporter.errorCount == 0 && sanityCheck(precondition, false, body))
      solver.checkSat(z3constraint) match {
        case (UNSAT, _) => Some(true)
        case (SAT, model) =>
          //println("Model found: " + model)
          // TODO: print the models that are actually useful, once we figure out which ones those are
          // Return Some(false) if we have a valid model
          None
        case _ =>
          None
      }
    //else
     // None
  }

  case class Approximation(name: String, cnstrs: List[Expr])

  def getApproximation(vc: VerificationCondition): Approximation = {
    // Step one: full constraint, i.e. translation from ArithF into the (1 + delta) stuff
    //Approximation("z3Only", List(And(And(vc.pre, vc.body), negate(vc.post))))// Implies(And(vc.pre, vc.body), vc.post)))
    

    println("before: " + vc.body)
    val transformer = new FloatApproximator(reporter, solver, options, vc.pre, vc.variables)
    val newBody = transformer.transform(vc.body)

    println("after: " + newBody)
    Approximation("xfloat", List(And(And(vc.pre, newBody), negate(vc.post))))
  }

}