package leon
package numerics

import ceres.common.{Rational, RationalInterval}

import affine._
import purescala.Trees._
import purescala.Common._
import purescala.TypeTrees._

import Utils._
import ApproximationType._

import collection.mutable.Queue


class SpecGen(reporter: Reporter, prover: Prover) {

  def generateSpec(vc: VerificationCondition) = {
    reporter.info("")
    reporter.info("----------> generating postcondition for: " + vc.funDef.id.name)

    vc.specConstraint match {
      case Some(c) =>
        val approxConstraint = c.approximationForSpec match {
            case Some(a) => a
            case None =>
              prover.getNextApproximation(PostInlining_AA, c, vc.inputs)
          }

        val approx = approxConstraint.values.filter( k => k._1 == ResultVariable())
        val newConstraint = actualConstraintFromResults(approx)
        vc.generatedPost = Some(newConstraint)
        println(vc.generatedPost)

      case None =>
        reporter.warning("Forgotten spec constraint?")
    }


  }

  def generateSpecMoreInfo(vc: VerificationCondition) = {
    reporter.info("")
    reporter.info("----------> generating postcondition for: " + vc.funDef.id.name)

    vc.specConstraint match {
      case Some(c) =>
        var args = Seq[Expr]()
        for (path <- c.paths) {
          // TODO: add error on computing the path condition
          val cond = path.condition
          val res = path.values(ResultVariable())

          res.interval

          val errorExpr = getErrorExpression(res.error, path.indices)
          args = args :+ And(Seq(cond, LessEquals(RationalLiteral(res.interval.xlo), ResultVariable()),
            LessEquals(ResultVariable(), RationalLiteral(res.interval.xhi)),
            Noise(ResultVariable(), errorExpr)))
        }


        val newConstraint = Or(args)
        reporter.info("computed spec: " + newConstraint)
        vc.generatedPost = Some(newConstraint)

      case None =>
        reporter.warning("Forgotten spec constraint?")
    }
  }

  def getErrorExpression(a: XRationalForm, indices: Map[Int, Expr]): Expr = {
    val indexSet: Set[Int] = indices.keys.toSet
    val (lin, rest) = a.noise.partition(d => indexSet(d.index))

    val maxError = affine.Utils.sumSeq(rest)
    val restError = RationalInterval(-maxError, maxError) + RationalInterval(a.x0, a.x0)

    val restErrorVar = getNewErrorVar
    var cnstr: Expr = restErrorVar

    for (dev <- lin) {
      // TODO: not quite right! it should be the error on variable, or rather whether it was there or not...
      cnstr = Plus(cnstr, Times(RationalLiteral(dev.value), getNamedError(indices(dev.index))))
    }
    And(ratint2expr(restError, restErrorVar), cnstr)
  }

}