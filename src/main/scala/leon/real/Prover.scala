/* Copyright 2013-2014 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import purescala.Definitions._
import purescala.TreeOps._

import real.Trees.{Noise, Roundoff, Actual}
import real.TreeOps._
import Sat._
import Valid._
import Approximations._
import FncHandling._
import ArithmApprox._
import PathHandling._
import Rational._



class Prover(ctx: LeonContext, options: RealOptions, prog: Program, fncs: Map[FunDef, Fnc]) {
  implicit val debugSection = utils.DebugSectionReals
  val reporter = ctx.reporter
  val solver = new RangeSolver(options.z3Timeout)
  val approx = new Approximations(options, fncs, reporter, solver)

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
    reporter.debug("VCs: " + vcs)
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
          val currentApprox = approx.getApproximation(vc, aKind, precision, postMap)
          spec = mergeSpecs(spec, currentApprox.spec)
          postMap += (vc.funDef -> currentApprox.spec)

          if (vc.kind == VCKind.SpecGen) true  // specGen, no need to check, only uses first approximation
          else
            checkValid(currentApprox, vc.variables, precision) match {
              case VALID =>
                reporter.info("==== VALID ====")
                vc.value += (precision -> VALID)
                true
              case INVALID =>
                reporter.info("=== INVALID ===")
                vc.value += (precision -> INVALID)
                true
              case UNKNOWN =>
                reporter.info("---- Unknown ----")
                false
              case NothingToShow =>
                vc.value += (precision -> NothingToShow)
                true
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

    vcs.forall( vc => vc.kind == VCKind.SpecGen || vc.value(precision) != UNKNOWN )
  }

  def checkValid(app: Approximation, variables: VariablePool, precision: Precision): Valid = {
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
              val realOnlyConstraint = removeErrorsAndActual(And(And(cnstr.precondition, realCnstr), negate(cnstr.postcondition)))
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
    if (app.constraints.isEmpty) NothingToShow
    else if ( (validCount + invalidCount) < app.constraints.length) UNKNOWN
    else if (invalidCount > 0) INVALID
    else VALID
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
