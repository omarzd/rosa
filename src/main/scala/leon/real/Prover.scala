/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import purescala.Definitions._
import purescala.TreeOps._

import Precision._
import Sat._
import FncHandling._
import ArithmApprox._
import PathHandling._


case class Approximation(kind: ApproxKind, cnstrs: Seq[Expr])

class Prover(ctx: LeonContext, options: RealOptions, prog: Program) {
  val reporter = ctx.reporter
  val solver = new RealSolver(ctx, prog, options.z3Timeout)
  
  def check(vcs: Seq[VerificationCondition]) = {
    for (vc <- vcs) {
      reporter.info("Verification condition (%s) ==== %s ====".format(vc.kind, vc.id))
      reporter.info("Trying with approximation")
      val start = System.currentTimeMillis

      val currentApprox = getApproximation(vc, ApproxKind(Uninterpreted, Merging, JustFloat))
      reporter.info("  - " + currentApprox.kind)
      println(currentApprox.cnstrs)
      checkValid(currentApprox, vc.variables) match {
        case Some(true) =>
          reporter.info("==== VALID ====")
          vc.value = Some(true)
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

    // TODO: arithmetic simplification

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

  def getApproximation(vc: VerificationCondition, kind: ApproxKind): Approximation = {

    val (preTmp, bodyTmp, postTmp) = kind.fncHandling match {
      case Uninterpreted => (vc.pre, vc.body, vc.post)

      case Postcondition =>
        throw new Exception("Ups, not yet implemented.")
        (True, True, True)
      case Inlining =>
        throw new Exception("Ups, not yet implemented.")
        (True, True, True)
    }

    val paths: List[(Expr, Expr, Expr)] = kind.pathHandling match {
      case Pathwise =>
        throw new Exception("Ups, not yet implemented.")
        List((True, True, True))
      case Merging =>
        List( (preTmp, bodyTmp, postTmp) )
    }

    
    kind.arithmApprox match {
      case Z3Only =>
        var approx = Seq[Expr]()
        for ( (pre, body, post) <- paths) {
          approx :+= And(And(vc.pre, vc.body), negate(vc.post))  // Implies(And(vc.pre, vc.body), vc.post)))
        }
        Approximation(kind, approx)
      case JustFloat =>
        var approx = Seq[Expr]()
  
        for ( (pre, body, post) <- paths) {
          println("before: " + body)
          // Hmm, this uses the same solver as the check...
          val transformer = new FloatApproximator(solver, options, pre, vc.variables)
          val newBody = transformer.transform(body)

          println("after: " + newBody)
          approx :+= And(And(pre, newBody), negate(post))
        }
        Approximation(kind, approx)
      case FloatNRange =>
        Approximation(kind, List())
    }
  }

}