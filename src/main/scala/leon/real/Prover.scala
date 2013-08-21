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
import Rational._

case class Approximation(kind: ApproxKind, cnstrs: Seq[Expr], spec: Option[Spec])

class Prover(ctx: LeonContext, options: RealOptions, prog: Program) {
  val reporter = ctx.reporter
  val solver = new RealSolver(ctx, prog, options.z3Timeout)
  
  def check(vcs: Seq[VerificationCondition]) = {
    for (vc <- vcs) {
      reporter.info("Verification condition (%s) ==== %s ====".format(vc.kind, vc.id))
      reporter.info("Trying with approximation")
      val start = System.currentTimeMillis

      // TODO: filter out those that are not applicable
      val approximations = List(ApproxKind(Uninterpreted, Merging, JustFloat))
      var spec: Option[Spec] = None

      approximations.find(aKind => {
        val currentApprox = getApproximation(vc, aKind)
        spec = merge(spec, currentApprox.spec)
        reporter.info("  - " + currentApprox.kind)
        println(currentApprox.cnstrs)
        checkValid(currentApprox, vc.variables) match {
          case Some(true) =>
            reporter.info("==== VALID ====")
            vc.value = Some(true)
            true
          case Some(false) =>
            reporter.info("=== INVALID ===")
            true
          case None =>
            reporter.info("---- Unknown ----")
            false
        }

      }) match {
        case None => {
          //vcInfo.hasValue = true
          //reporter.warning("No solver could prove or disprove the verification condition.")
        }
        case _ =>
      }
      println("generated spec: " + spec)
      vc.spec = spec
      
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
        Approximation(kind, approx, None)
      case JustFloat =>
        var approx = Seq[Expr]()
        var spec: Option[Spec] = None
  
        for ( (pre, body, post) <- paths) {
          println("before: " + body)
          // Hmm, this uses the same solver as the check...
          val transformer = new FloatApproximator(solver, options, pre, vc.variables)
          val (newBody, newSpec) = transformer.transformWithSpec(body)
          spec = merge(spec, Option(newSpec))
          println("after: " + newBody)
          approx :+= And(And(pre, newBody), negate(post))
        }
        Approximation(kind, approx, spec)
      case FloatNRange =>
        Approximation(kind, List(), None)
    }
  }

  private def merge(currentSpec: Option[Spec], newSpec: Option[Spec]): Option[Spec] = (currentSpec, newSpec) match {
    case (Some(s1), Some(s2)) =>
      val lowerBnd = max(s1.bounds.xlo, s2.bounds.xlo)
      val upperBnd = min(s1.bounds.xhi, s2.bounds.xhi)
      val err = min(s1.absError, s2.absError)
      Some(Spec(RationalInterval(lowerBnd, upperBnd), err))
    case (None, Some(s)) => newSpec
    case _ => currentSpec
  }

}