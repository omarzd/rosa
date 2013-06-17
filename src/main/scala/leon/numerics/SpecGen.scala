package leon
package numerics

import ceres.common.{Rational, RationalInterval}

import affine._
import purescala.Trees._
import purescala.Common._
import purescala.TypeTrees._

import Utils._

import collection.mutable.Queue

object SpecGen {
  // TODO: collect all these somewhere, like in Utils?
  private var errCounter = 0
  def getNewErrorVar: Variable = {
    errCounter = errCounter + 1
    Variable(FreshIdentifier("#err_" + errCounter)).setType(RealType)
  }

  def getNamedError(v: Expr): Variable = {
    Variable(FreshIdentifier("#err_(" + v.toString + ")")).setType(RealType)
  }

}

class SpecGen(reporter: Reporter) {
  import SpecGen._

  def generateSpec(vc: VerificationCondition) = {
    reporter.info("")
    reporter.info("----------> generating postcondition for: " + vc.funDef.id.name)

    vc.specConstraint match {
      case Some(c) =>
        val approx = mergeActualPathResults(c.paths).filter( k => k._1 == ResultVariable())
        val newConstraint = constraintFromResults(approx)
        reporter.info("computed spec: " + newConstraint)
        vc.generatedPost = Some(newConstraint)

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
    val (lin:Queue[Deviation], rest:Queue[Deviation]) = a.noise.partition(d => indexSet(d.index))

    val maxError = affine.Utils.sumQueue(rest)
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