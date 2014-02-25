/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import purescala.Definitions._

import real.Trees.{Noise, Roundoff, Actual}
import real.TreeOps._
import Rational._

class Approximations(options: RealOptions, fncs: Map[FunDef, Fnc],
  reporter: Reporter, solver: RealSolver) {
  import Approximations._
  import FncHandling._
  import ArithmApprox._
  import PathHandling._

  implicit val debugSection = utils.DebugSectionReals

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
          spec = mergeSpecs(spec, nextSpecs)
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

  
}

object Approximations {

  // to avoid confusion with nested sequences
  type SpecTuple = Seq[Spec]

  def mergeSpecs(currentSpec: SpecTuple, newSpecs: SpecTuple): SpecTuple = (currentSpec, newSpecs) match {
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


  case class Constraint(precondition: Expr, realComp: Expr, finiteComp: Expr, postcondition: Expr) 

  /*  Spec is the overall computed postcondition
    @param kind which approximation type we used
    @param contraints one constraint per path
    @param spec overall computed (merged) specification
  */
  case class Approximation(kind: ApproxKind, constraints: Seq[Constraint], spec: SpecTuple) {
    // one spec per path
    var specsPerPath: Seq[SpecTuple] = Seq.empty
  }

  object FncHandling extends Enumeration {
    type FncHandling = Value
    val Uninterpreted = Value("Uninterpreted")
    val Postcondition = Value("Postcondition")
    val Inlining = Value("Inlining")
  }
  import FncHandling._

  object PathHandling extends Enumeration {
    type PathHandling = Value
    val Pathwise = Value("Pathwise")
    val Merging = Value("Merging")
  }
  import PathHandling._

  object ArithmApprox extends Enumeration {
    type ArithmApprox = Value
    val Z3Only = Value("Z3Only")
    val JustFloat = Value("JustFloat") // evaluate the float. part with xfloat
    val FloatNRange = Value("Float'n'Range") // also replace the real with an approx. of the range
  }
  import ArithmApprox._

  case class ApproxKind(fncHandling: FncHandling.Value, pathHandling: PathHandling.Value, arithmApprox: ArithmApprox.Value) {
    val allowsRealModel = (fncHandling == Uninterpreted && arithmApprox == JustFloat) || // no functions
                          (fncHandling == Inlining && arithmApprox == JustFloat) || // with fncs
                          (fncHandling == Inlining && arithmApprox == Z3Only) // with fncs
  }

  val a_FncIf = List(
    ApproxKind(Uninterpreted, Merging, Z3Only),
    ApproxKind(Uninterpreted, Pathwise, Z3Only),

    ApproxKind(Postcondition, Merging, Z3Only),
    ApproxKind(Postcondition, Merging, JustFloat),
    ApproxKind(Postcondition, Merging, FloatNRange),
    ApproxKind(Postcondition, Pathwise, Z3Only),
    ApproxKind(Postcondition, Pathwise, JustFloat),
    ApproxKind(Postcondition, Pathwise, FloatNRange),
    ApproxKind(Inlining, Merging, Z3Only),
    ApproxKind(Inlining, Merging, JustFloat),
    ApproxKind(Inlining, Merging, FloatNRange),
    ApproxKind(Inlining, Pathwise, Z3Only),
    ApproxKind(Inlining, Pathwise, JustFloat),
    ApproxKind(Inlining, Pathwise, FloatNRange)
    )

  val a_FncNoIf = List(
    ApproxKind(Uninterpreted, Merging, Z3Only),

    ApproxKind(Postcondition, Merging, Z3Only),
    ApproxKind(Postcondition, Merging, JustFloat),
    ApproxKind(Postcondition, Merging, FloatNRange),
    ApproxKind(Inlining, Merging, Z3Only),
    ApproxKind(Inlining, Merging, JustFloat),
    ApproxKind(Inlining, Merging, FloatNRange)
    )


  val a_NoFncIf = List(
    ApproxKind(Uninterpreted, Merging, Z3Only),
    ApproxKind(Uninterpreted, Merging, JustFloat),
    ApproxKind(Uninterpreted, Merging, FloatNRange),
    ApproxKind(Uninterpreted, Pathwise, Z3Only),
    ApproxKind(Uninterpreted, Pathwise, JustFloat),
    ApproxKind(Uninterpreted, Pathwise, FloatNRange)
    )

  val a_NoFncNoIf = List(
    ApproxKind(Uninterpreted, Merging, Z3Only),
    ApproxKind(Uninterpreted, Merging, JustFloat),
    ApproxKind(Uninterpreted, Merging, FloatNRange)
    )


  // approximations are tried in this order
  /*val allApprox = List(
    ApproxKind(Uninterpreted, Merging, Z3Only),
    ApproxKind(Uninterpreted, Merging, JustFloat),
    ApproxKind(Uninterpreted, Merging, FloatNRange),
    ApproxKind(Uninterpreted, Pathwise, Z3Only),
    ApproxKind(Uninterpreted, Pathwise, JustFloat),
    ApproxKind(Uninterpreted, Pathwise, FloatNRange),

    ApproxKind(Postcondition, Merging, Z3Only),
    ApproxKind(Postcondition, Merging, JustFloat),
    ApproxKind(Postcondition, Merging, FloatNRange),
    ApproxKind(Postcondition, Pathwise, Z3Only),
    ApproxKind(Postcondition, Pathwise, JustFloat),
    ApproxKind(Postcondition, Pathwise, FloatNRange),

    ApproxKind(Inlining, Merging, Z3Only),
    ApproxKind(Inlining, Merging, JustFloat),
    ApproxKind(Inlining, Merging, FloatNRange),
    ApproxKind(Inlining, Pathwise, Z3Only),
    ApproxKind(Inlining, Pathwise, JustFloat)
    ApproxKind(Inlining, Pathwise, FloatNRange)
    )
  */

}
