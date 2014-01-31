/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Trees.Expr

object Approximations {

  // to avoid confusion with nested sequences
  type SpecTuple = Seq[Spec]

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
