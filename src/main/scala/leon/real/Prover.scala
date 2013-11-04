/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import purescala.Definitions._
import purescala.TreeOps._

import real.Trees.{FResVariable, ResultVariable, Noise, Roundoff, Actual}
import real.TreeOps._
import Sat._
import Approximations._
import FncHandling._
import ArithmApprox._
import PathHandling._
import Rational._



class Prover(ctx: LeonContext, options: RealOptions, prog: Program, fncs: Map[FunDef, Fnc], verbose: Boolean = false) {
  implicit val debugSection = DebugSectionVerification
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
  
  // Returns the precision with which we can satisfy all constraints, or the last one tried,
  // as well as an indication whether verification was successfull.
  def check(vcs: Seq[VerificationCondition]): (Precision, Boolean) = {
    val validApproximations = getApplicableApproximations(vcs)

    val precisions = options.precision
    println("precisions: " + precisions)

    def findPrecision(precIndex: Int): (Precision, Boolean) = {
      println("index: " + precIndex)
      if (precIndex < 0) (precisions.head, false)
      else if (precIndex > precisions.length) (precisions.last, false)
      else {
        if (checkVCsInPrecision(vcs, precisions(precIndex - 1), validApproximations)) {
          // we could solve it, so try a smaller precision if it exists
          //val newPrec = precIndex / 2
          (precisions(precIndex - 1), true)
        } else {
          // verification unsuccessfull, try higher
          println("unsuccessfull")
          val newPrec = precIndex + ((precisions.length - precIndex - 1) / 2 + 1)
          findPrecision(newPrec)
        }
      }
    }

    if (verbose) {
      reporter.debug("approximation kinds:")
      validApproximations.foreach(x => reporter.debug(x._1 + ": " + x._2))
    }
    
    findPrecision(1)
    //findPrecision((precisions.length - 1) / 2 + 1)
  }

  // TODO: align code
  def checkVCsInPrecision(vcs: Seq[VerificationCondition], precision: Precision,
    validApproximations: Map[VerificationCondition, List[ApproxKind]]): Boolean = {
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
          if (vc.kind == VCKind.SpecGen) true  // specGen, no need to check, only uses first approximation
          else
            checkValid(currentApprox, vc.variables, precision) match {
              case Some(true) =>
                reporter.info("==== VALID ====")
                vc.value += (precision -> Some(true))
                true
              case Some(false) =>
                reporter.info("=== INVALID ===")
                vc.value += (precision -> Some(false))
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
          case e: FixedPointOverflowException =>
            reporter.warning("Insufficient bitwidth: " + e.getMessage)
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
  }

  def checkValid(app: Approximation, variables: VariablePool, precision: Precision): Option[Boolean] = {
    if (verbose) reporter.debug("checking for valid: " + app.constraints)

    val transformer = new LeonToZ3Transformer(variables, precision)
    var valid: Option[Boolean] = None
    
    for ((cnstr, index) <- app.constraints.zipWithIndex) {
      val sanityConstraint = And(cnstr.precondition, And(cnstr.realComp, cnstr.finiteComp))
      val toCheck = And(sanityConstraint, negate(cnstr.postcondition))
      
      val z3constraint = massageArithmetic(transformer.getZ3Expr(toCheck))
      val sanityExpr = massageArithmetic(transformer.getZ3Expr(sanityConstraint))

      //if (verbose) 
      reporter.debug("z3constraint ("+index+"): " + z3constraint)

      if (reporter.errorCount == 0 && sanityCheck(sanityExpr)) {
        solver.checkSat(z3constraint) match {
          case (UNSAT, _) => valid = Some(true);
          case (SAT, model) =>
            if (app.kind.allowsRealModel) {
              // Idea: check if we get a counterexample for the real part only, that is then a possible counterexample, (depends on the approximation)
              val realFilter = new RealFilter
              val realOnlyConstraint = realFilter.transform(And(And(cnstr.precondition, cnstr.realComp), negate(cnstr.postcondition)))
              //println("\nreal only: " + realOnlyConstraint)
              val massaged = massageArithmetic(transformer.getZ3Expr(realOnlyConstraint))
              //println("real only constraint: " + massaged)
              solver.checkSat(massaged) match {
                case (SAT, model) =>
                  // TODO: pretty print the models
                  reporter.info("counterexample: " + model)
                  valid = Some(false)
                case (UNSAT, _) =>
                case _ =>
              }
            }


          case _ =>;
        }
      }
    }
    valid
  }

  

  // DOC: we only support function calls in fnc bodies, not in pre and post
  def getApproximation(vc: VerificationCondition, kind: ApproxKind, precision: Precision): Approximation = {
    val postInliner = new PostconditionInliner
    val fncInliner = new FunctionInliner(fncs)

    val (pre, bodyFnc, post) = kind.fncHandling match {
      case Uninterpreted =>
        (vc.pre, vc.body, vc.post)

      case Postcondition =>
        (vc.pre, postInliner.transform(vc.body), vc.post)

      case Inlining =>
        (vc.pre, fncInliner.transform(vc.body), vc.post)
    }
    if (verbose) reporter.debug("after FNC handling:\npre: %s\nbody: %s\npost: %s".format(pre,bodyFnc,post))


    val paths: Set[Path] = kind.pathHandling match {
      case Pathwise => getPaths(bodyFnc).map {
        case (cond, expr) => Path(cond, expr, idealToActual(expr, vc.variables))
      }
        
      case Merging =>  Set(Path(True, bodyFnc, idealToActual(bodyFnc, vc.variables)))
    }
    if (verbose) reporter.debug("after PATH handling:\nbody: %s".format(paths.mkString("\n")))

    
    kind.arithmApprox match {
      case Z3Only =>
        var constraints = Seq[Constraint]()
        //var approx = Seq[Expr]()
        //var sanity = Seq[Expr]()
        for (path <- paths) {
          //approx :+= And(And(pre, And(path.condition, path.body)), negate(post))  // Implies(And(vc.pre, vc.body), vc.post)))
          //sanity :+= And(pre, And(path.condition, path.body))
          constraints :+= Constraint(And(pre, path.condition), path.bodyReal, path.bodyFinite, post)
        }
        Approximation(kind, constraints, None)

      case JustFloat =>
        var constraints = Seq[Constraint]()
        //var approx = Seq[Expr]()
        //var sanity = Seq[Expr]()
        var spec: Option[Spec] = None
  
        for ( path <- paths ) {
          //println("\nfor path: " + path)
          // Hmm, this uses the same solver as the check...
          // TODO: one for all?
          val transformer = new FloatApproximator(reporter, solver, precision, And(pre, path.condition), vc.variables, options.pathError)
          val (bodyFiniteApprox, nextSpec) = transformer.transformWithSpec(path.bodyFinite)
          spec = merge(spec, nextSpec)
          if (verbose) reporter.debug("body after approx: " + bodyFiniteApprox)
          //approx :+= And(And(pre, And(path.condition, newBody)), negate(post))
          //sanity :+= And(pre, newBody)
          //precondition: Expr, realComp: Expr, finiteComp: Expr, postcondition: Expr)
          constraints :+= Constraint(And(pre, path.condition), path.bodyReal, bodyFiniteApprox, post)
        }
        Approximation(kind, constraints, spec)

      case FloatNRange => 
        // TODO: real range approximation
        throw new Exception("FloatNRange doesn't exist yet")
        Approximation(kind, List(), None)
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