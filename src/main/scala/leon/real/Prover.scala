/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import purescala.Definitions._
import purescala.TreeOps._

import real.TreeOps._
import Precision._
import Sat._
import Approximations._
import FncHandling._
import ArithmApprox._
import PathHandling._
import Rational._



class Prover(ctx: LeonContext, options: RealOptions, prog: Program, fncs: Map[FunDef, Fnc], verbose: Boolean = false) {
  val reporter = ctx.reporter
  val solver = new RealSolver(ctx, prog, options.z3Timeout)

  // TODO: ugly?!
  def getApplicableApproximations(vcs: Seq[VerificationCondition]): Map[VerificationCondition, List[ApproxKind]] =
    vcs.map { vc =>
        val list = (
          if (vc.allFncCalls.isEmpty) {
            if (containsIfExpr(vc.body))
              if (options.pathError) a_NoFncIf.filter(ak => ak.pathHandling == Merging)
              else a_NoFncIf
            else a_NoFncNoIf
          } else {
            if (containsIfExpr(vc.body))
              if (options.pathError) a_FncIf.filter(ak => ak.pathHandling == Merging)
              else a_FncIf
            else a_FncNoIf
          })

        if (!options.z3Only) (vc, list.filter(ak => ak.arithmApprox != Z3Only))
        else (vc, list)
      }.toMap
  
  def check(vcs: Seq[VerificationCondition]): Precision = {
    val validApproximations = getApplicableApproximations(vcs)

    if (verbose) {
      reporter.debug("approximation kinds:")
      validApproximations.foreach(x => reporter.debug(x._1 + ": " + x._2))
    }
    options.precision.find( precision => {
      reporter.info("Trying precision: " + precision)

      for (vc <- vcs if (options.specGen || vc.kind != VCKind.SpecGen)) {
        reporter.info("Verification condition  ==== %s (%s) ====".format(vc.fncId, vc.kind))
        if (verbose) reporter.debug("pre: " + vc.pre)
        if (verbose) reporter.debug("body: " + vc.body)
        if (verbose) reporter.debug("post: " + vc.post)
        
        val start = System.currentTimeMillis
        var spec: Option[Spec] = None

        val approximations = validApproximations(vc)
        
        // TODO: re-use some of the approximation work across precision?
        approximations.find(aKind => {
          reporter.info("approx: " + aKind)

          try {
            val currentApprox = getApproximation(vc, aKind, precision)
            spec = merge(spec, currentApprox.spec)
          
            //if (verbose) println(currentApprox.cnstrs)
            if (vc.kind == VCKind.SpecGen) true  // only uses first approximation
            else
              checkValid(currentApprox, vc.variables, precision) match {
                case Some(true) =>
                  reporter.info("==== VALID ====")
                  vc.value += (precision -> Some(true))
                  true
                case Some(false) =>
                  // TODO: figure out if we can find invalid
                  reporter.info("=== INVALID ===")
                  true
                case None =>
                  reporter.info("---- Unknown ----")
                  false
              } 
          } catch {
            case PostconditionInliningFailedException(msg) =>
              reporter.info("failed to compute approximation: " + msg)
              false
            case e: RealArithmeticException =>
              reporter.warning("Failed to compute approximation: " + e.getMessage)
              false
          }

        }) match {
          case None =>
          case _ =>
        }
        
        vc.spec += (precision -> spec)
      
        val end = System.currentTimeMillis
        vc.time = Some(end - start)
        reporter.info("generated spec: " + spec + " in " + (vc.time.get / 1000.0))
      }
      vcs.forall( vc => {
        vc.value(precision) match {
          case None => false 
          case _ => true
        }
      })

    }) match {
      case Some(p) => p
      case None => options.precision.last
    }
    
  }

  def checkValid(app: Approximation, variables: VariablePool, precision: Precision): Option[Boolean] = {
    if (verbose) reporter.debug("checking for valid: " + app.cnstrs)

    // I think we can keep one
    val transformer = new LeonToZ3Transformer(variables)
    var valid: Option[Boolean] = Some(true)

    for (((constraint, sanityExpr), index) <- app.cnstrs.zip(app.sanityChecks).view.zipWithIndex) {
      //println("constraint: " + constraint)

      val z3constraint = if (useMassageArithmetic) massageArithmetic(transformer.getZ3Expr(constraint, precision))
                        else transformer.getZ3Expr(constraint, precision)
      
      if (verbose) reporter.debug("z3constraint ("+index+"): " + z3constraint)

      if (reporter.errorCount == 0 && sanityCheck(transformer.getZ3Expr(sanityExpr, precision)))
        solver.checkSat(z3constraint) match {
          case (UNSAT, _) =>;
          case (SAT, model) =>
            //println("Model found: " + model)
            // TODO: print the models that are actually useful, once we figure out which ones those are
            // Return Some(false) if we have a valid model
            valid = None
          case _ =>
            valid = None
        }
      else
        valid = None
    }
    valid
  }

  // DOC: we only support function calls in fnc bodies, not in pre and post
  def getApproximation(vc: VerificationCondition, kind: ApproxKind, precision: Precision): Approximation = {
    val postInliner = new PostconditionInliner
    val fncInliner = new FunctionInliner(fncs)

    val (preFnc, bodyFnc, postFnc) = kind.fncHandling match {
      case Uninterpreted =>
        (vc.pre, vc.body, vc.post)

      case Postcondition =>
        (vc.pre, postInliner.transform(vc.body), vc.post)

      case Inlining =>
        (vc.pre, fncInliner.transform(vc.body), vc.post)
    }
    if (verbose)
      reporter.debug("after FNC handling:\npre: %s\nbody: %s\npost: %s".format(preFnc,bodyFnc,postFnc))


    val (pre, body, post): (Expr, Set[Path], Expr) = kind.pathHandling match {
      case Pathwise =>
        ( preFnc,
          getPaths(bodyFnc).map(p => Path(p.condition, And(p.body, idealToActual(p.body, vc.variables)))), 
          postFnc )
      case Merging =>
        ( preFnc,
          Set(Path(True, And(bodyFnc, idealToActual(bodyFnc, vc.variables)))),
          postFnc )
    }
    if (verbose)
      reporter.debug("after PATH handling:\npre: %s\nbody: %s\npost: %s".format(pre,body.mkString("\n"),post))

    
    kind.arithmApprox match {
      case Z3Only =>
        var approx = Seq[Expr]()
        var sanity = Seq[Expr]()
        for (path <- body) {
          approx :+= And(And(pre, And(path.condition, path.body)), negate(post))  // Implies(And(vc.pre, vc.body), vc.post)))
          sanity :+= And(pre, And(path.condition, path.body))
        }
        Approximation(kind, approx, sanity, None)

      case JustFloat =>
        var approx = Seq[Expr]()
        var sanity = Seq[Expr]()
        var spec: Option[Spec] = None
  
        for ( path <- body ) {
          //println("\nfor path: " + path)
          // Hmm, this uses the same solver as the check...
          val transformer = new FloatApproximator(reporter, solver, precision, And(pre, path.condition),
            vc.variables, options.pathError)
          val (newBody, newSpec) = transformer.transformWithSpec(path.body)
          spec = merge(spec, newSpec)
          if (verbose) reporter.debug("body after approx: " + newBody)
          approx :+= And(And(pre, And(path.condition, newBody)), negate(post))
          sanity :+= And(pre, newBody)
        }
        Approximation(kind, approx, sanity, spec)

      case FloatNRange => 
        // TODO: real range approximation
        throw new Exception("FloatNRange doesn't exist yet")
        Approximation(kind, List(), List(), None)
    }
  }

  private def merge(currentSpec: Option[Spec], newSpec: Option[Spec]): Option[Spec] = (currentSpec, newSpec) match {
    case (Some(s1), Some(s2)) =>
      val lowerBnd = min(s1.bounds.xlo, s2.bounds.xlo)
      val upperBnd = max(s1.bounds.xhi, s2.bounds.xhi)
      val err = max(s1.absError, s2.absError)
      Some(Spec(RationalInterval(lowerBnd, upperBnd), err))
    case (None, Some(s)) => newSpec
    case _ => currentSpec
  }

  // if true, we're sane
  // TODO: make this a method in the solver and then we don't need to duplicate
  private def sanityCheck(pre: Expr, body: Expr = BooleanLiteral(true)): Boolean = {
    val sanityCondition = And(pre, body)
    solver.checkSat(sanityCondition) match {
      case (SAT, model) => true
      case (UNSAT, model) =>
        reporter.warning("Not sane! " + sanityCondition)
        false
      case _ =>
        reporter.info("Sanity check failed! ")// + sanityCondition)
        false
    }
  }
}