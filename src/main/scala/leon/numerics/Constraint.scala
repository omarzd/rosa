package leon
package numerics


import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import Valid._

import Utils._

// This is an approximation of an constraint.
case class ConstraintApproximation(pre: Expr, body: Expr, post: Expr, name: String) {
  lazy val paths = collectPaths(body)
  override def toString: String = "APP(%s && %s) ==> %s".format(pre.toString, body.toString, post.toString)
}

// An original (unapproximated constraint) derived from somewhere in the program.
case class Constraint(pre: Expr, body: Expr, post: Expr, description: String) {
  var status: Option[Valid] = None
  var model: Option[Map[Identifier, Expr]] = None
  var strategy: String = ""

  def numVariables: Int = variablesOf(pre).size + variablesOf(body).size
  def size: Int = formulaSize(pre) + formulaSize(body)

  def solved: Boolean = status match {
    case Some(VALID) | Some(INVALID) => true
    case _ => false
  }

  lazy val paths = collectPaths(body)

  private var approximations = Seq[Option[ConstraintApproximation]]()
  // Maaaagic numbers!
  def hasNextApproximation = (approximations.size < 1)

  // returns None, if nothing left to try
  def getNextApproximation: Option[ConstraintApproximation] = {
    val c = approximations.size match {
      case 0 =>
        Some(ConstraintApproximation(pre, body, post, "no approx."))  // nothing with uninterpreted functions

      case _ => None

      /*val (pre, paths, post) =
        if (containsFunctionCalls(c.body)) {
          println(".............")
          // strategy no. 1: replace function call with fresh variable and add constraints based on the postcondition of function
          // assume precondition holds, is being checked separately
          val postinliner = new PostconditionInliner
          val bodyWOFncs = postinliner.transform(c.body)
          val constraints = postinliner.constraints
          println("body without fncs: " + bodyWOFncs)
          println("constraints: " + constraints)
          (And(c.pre, And(constraints)), collectPaths(bodyWOFncs), c.post)
        } else {
          (c.pre, c.paths, c.post)
        }*/

        /*c.status match {
        case (None | Some(DUNNO) | Some(NOT_SURE)) =>
          reporter.info("Now trying with XFloat only...")
          val newConstraint = approximateConstraint(c, vc.inputs)
          reporter.info("AA computed: " + newConstraint)
          c.overrideStatus(checkWithZ3(newConstraint, Set[Path](), c.post, vc.allVariables), "AA only")
          println("XFloat only result: " + c.status)

        case _ =>;
      }*/

      // TODO: If neither work, do partial approx.
    }

    approximations = approximations :+ c
    c
  }


  // whether we already ran the AA approximation
  var approximated: Boolean = false

  def overrideStatus(s: (Option[Valid], Option[Map[Identifier, Expr]])) = {
    status = s._1
    model = s._2
  }

  override def toString: String = "(%s && %s) ==> %s".format(pre.toString, body.toString, post.toString)

}


