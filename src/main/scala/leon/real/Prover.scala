/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import purescala.Definitions._
import purescala.TreeOps._

import real.Trees.{Noise, Roundoff, Actual}
import real.TreeOps._
import Sat._
import Approximations._
import FncHandling._
import ArithmApprox._
import PathHandling._
import Rational._



class Prover(ctx: LeonContext, options: RealOptions, prog: Program, fncs: Map[FunDef, Fnc]) {
  implicit val debugSection = utils.DebugSectionReals
  val reporter = ctx.reporter
  val solver = new RealSolver(ctx, prog, options.z3Timeout)

  // TODO: this is ugly!!!
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

    def findPrecision(lowerBnd: Int, upperBnd: Int): (Precision, Boolean) = {
      if (lowerBnd > upperBnd) (precisions.last, false)
      else {
        val mid = lowerBnd + (upperBnd - lowerBnd) / 2// ceiling int division
        reporter.info("Checking precision: " + precisions(mid))
        if (checkVCsInPrecision(vcs, precisions(mid), validApproximations)) {
          if (lowerBnd == mid) (precisions(lowerBnd), true)
          else {
            findPrecision(lowerBnd, mid)
          }
        }
        else {
          if (lowerBnd == mid && upperBnd < precisions.length - 1) (precisions(upperBnd), true)
          else {
            findPrecision(mid + 1, upperBnd)
          }
        }
      }
    }

    reporter.debug("approximation kinds:")
    validApproximations.foreach(x => reporter.debug(x._1 + ": " + x._2))
    
    findPrecision(0, precisions.length - 1)
  }

  def checkVCsInPrecision(vcs: Seq[VerificationCondition], precision: Precision,
    validApproximations: Map[VerificationCondition, List[ApproxKind]]): Boolean = {
    var postMap: Map[FunDef, Seq[Spec]] = vcs.map(vc => (vc.funDef -> Seq())).toMap

    //println("checking vcs: ")

    for (vc <- vcs if (options.specGen || vc.kind != VCKind.SpecGen)) {
      reporter.info("Verification condition  ==== %s (%s) ====".format(vc.fncId, vc.kind))
      reporter.debug("pre: " + vc.pre)
      reporter.debug("body: " + vc.body)
      reporter.debug("post: " + vc.post)

      val start = System.currentTimeMillis
      var spec: Seq[Spec] = Seq()

      val approximations = validApproximations(vc)

      // TODO: can we re-use some of the approximation work across precision?
      approximations.find(aKind => {
        reporter.info("approx: " + aKind)

        try {
          val currentApprox = getApproximation(vc, aKind, precision, postMap)
          spec = merge(spec, currentApprox.spec)
          postMap += (vc.funDef -> currentApprox.spec)

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
          case RealArithmeticException(msg) =>
            reporter.warning("Failed to compute approximation: " + msg)
            false
          case FixedPointOverflowException(msg) =>
            reporter.warning("Insufficient bitwidth: " + msg)
            false
          case SqrtNotImplementedException(msg) =>
            reporter.warning(msg)
            false
          case UnsoundBoundsException(msg) =>
            reporter.error(msg)
            return false
           
        }

      }) match {
        case None =>
        case _ =>
      }
      // TODO: there is a bug where not the correct spec is printed, see the InitialExample
      vc.spec += (precision -> spec)

      val end = System.currentTimeMillis
      vc.time = Some(end - start)
      reporter.info("generated spec: " + spec + " in " + (vc.time.get / 1000.0))
    }

    vcs.forall( vc => vc.kind == VCKind.SpecGen || !vc.value(precision).isEmpty )
  }

  def checkValid(app: Approximation, variables: VariablePool, precision: Precision): Option[Boolean] = {
    reporter.debug("checking for valid: " + app.constraints)

    val transformer = new LeonToZ3Transformer(variables, precision)
    var validCount = 0
    var invalidCount = 0

    for ((cnstr, index) <- app.constraints.zipWithIndex) {
      val realCnstr = addResults(cnstr.realComp, variables.resultVars)
      val finiteCnstr = addResultsF(cnstr.finiteComp, variables.fResultVars)

      val sanityConstraint = And(cnstr.precondition, And(realCnstr, finiteCnstr))
      val toCheck = And(sanityConstraint, negate(cnstr.postcondition))

      val z3constraint = massageArithmetic(transformer.getZ3Expr(toCheck))
      val sanityExpr = massageArithmetic(transformer.getZ3Expr(sanityConstraint))


      reporter.debug("z3constraint ("+index+"): " + z3constraint)

      if (reporter.errorCount == 0 && sanityCheck(sanityExpr)) {
        solver.checkSat(z3constraint) match {
          case (UNSAT, _) =>
            reporter.info(s"Constraint with $index is valid.")
            validCount += 1
          case (SAT, model) =>
            if (app.kind.allowsRealModel) {
              // Idea: check if we get a counterexample for the real part only, that is then a possible counterexample, (depends on the approximation)
              val realFilter = new RealFilter
              val realOnlyConstraint = realFilter.transform(And(And(cnstr.precondition, realCnstr), negate(cnstr.postcondition)))
              val massaged = massageArithmetic(transformer.getZ3Expr(realOnlyConstraint))
              solver.checkSat(massaged) match {
                case (SAT, model) =>
                  // TODO: pretty-print the models
                  reporter.info("counterexample: " + model)
                  invalidCount += 1 
                case (UNSAT, _) =>
                case _ =>
              }
            } else {
              reporter.info(s"Constraint with $index is unknown.")
            }


          case _ =>;
        }
      }
    }
    if ( (validCount + invalidCount) < app.constraints.length) None
    else if (invalidCount > 0) Some(false)
    else Some(true)
  }



  // DOC: we only support function calls in fnc bodies, not in pre and post
  def getApproximation(vc: VerificationCondition, kind: ApproxKind, precision: Precision, postMap: Map[FunDef, Seq[Spec]]): Approximation = {
    val postInliner = new PostconditionInliner(precision, postMap)
    val fncInliner = new FunctionInliner(fncs)
    val leonToZ3 = new LeonToZ3Transformer(vc.variables, precision)

    def isFeasible(pre: Expr): Boolean = {
      import Sat._
      solver.checkSat(leonToZ3.getZ3Expr(pre)) match {
        case (SAT, model) => true
        case (UNSAT, model) => false
        case _ =>
          reporter.error("Sanity check failed! ")// + sanityCondition)
          false
      }
    }

    val (pre, bodyFnc, post) = kind.fncHandling match {
      case Uninterpreted => (vc.pre, vc.body, vc.post)
      case Postcondition => (vc.pre, postInliner.transform(vc.body), vc.post)
      case Inlining => (vc.pre, fncInliner.transform(vc.body), vc.post)
    }
    if (kind.fncHandling != Uninterpreted) reporter.debug("after FNC handling:\npre: %s\nbody: %s\npost: %s".format(pre,bodyFnc,post))

    val paths: Set[Path] = kind.pathHandling match {
      case Pathwise => getPaths(bodyFnc).map {
        case (cond, expr) => Path(cond, expr, idealToActual(expr, vc.variables))
      }
      case Merging =>  Set(Path(True, bodyFnc, idealToActual(bodyFnc, vc.variables)))
    }
    reporter.debug("after PATH handling:\nbody: %s".format(paths.mkString("\n")))


    kind.arithmApprox match {
      case Z3Only =>
        var constraints = Seq[Constraint]()
        for (path <- paths) {
          constraints :+= Constraint(And(pre, path.condition), path.bodyReal, path.bodyFinite, post)
        }
        Approximation(kind, constraints, Seq())

      case JustFloat =>
        var constraints = Seq[Constraint]()
        var specsPerPath = Seq[SpecTuple]()
        var spec: SpecTuple = Seq() // seq since we can have tuples

        for ( path <- paths if (isFeasible(And(pre, path.condition))) ) {
          //solver.clearCounts
          val transformer = new Approximator(reporter, solver, precision, And(pre, path.condition), vc.variables, options.pathError)
          val (bodyFiniteApprox, nextSpecs) = transformer.transformWithSpec(path.bodyFinite, vc.kind == VCKind.Precondition)
          //println("solver counts: " + solver.getCounts)
          spec = merge(spec, nextSpecs)
          //if(!nextSpec.isEmpty)
          specsPerPath :+= nextSpecs//.get// else specsPerPath :+= DummySpec
          reporter.debug("body after approx: " + bodyFiniteApprox)
          constraints :+= Constraint(And(pre, path.condition), path.bodyReal, bodyFiniteApprox, post)
        }
        val approx = Approximation(kind, constraints, spec)
        vc.approximations += (precision -> (vc.approximations(precision) :+ approx))
        approx.specsPerPath = specsPerPath
        approx

      case FloatNRange => // assumes that a JustFloat approximation has already been computed
        val justFloatApprox = vc.approximations(precision).find(a =>
          a.kind.fncHandling == kind.fncHandling && a.kind.pathHandling == kind.pathHandling && a.kind.arithmApprox == JustFloat
          )

        justFloatApprox match {
          case Some(approx) =>
            val newConstraints =
              for (
                (cnstr, specs) <- approx.constraints.zip(approx.specsPerPath)
              ) yield
                Constraint(cnstr.precondition, And(specs.map(specToRealExpr(_))), cnstr.finiteComp, cnstr.postcondition)
            Approximation(kind, newConstraints, approx.spec)
          case None =>
            throw new RealArithmeticException("Cannot compute Float'n'Range approximation because JustFloat approximation is missing.")
            null
        }
    }
  }

  private def merge(currentSpec: SpecTuple, newSpecs: SpecTuple): SpecTuple = (currentSpec, newSpecs) match {
    case (Seq(), specs) => specs

    case (current, Seq()) => current

    case _ =>
      currentSpec.zip(newSpecs).map({
        case (s1, s2) =>
          val lowerBnd = min(s1.bounds.xlo, s2.bounds.xlo)
          val upperBnd = max(s1.bounds.xhi, s2.bounds.xhi)
          val err = max(s1.absError, s2.absError)
          assert(s1.id == s2.id)
          Spec(s1.id, RationalInterval(lowerBnd, upperBnd), err)
        })
  }

  // if true, we're sane
  // TODO: make a method in the solver and then we don't need to duplicate
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
