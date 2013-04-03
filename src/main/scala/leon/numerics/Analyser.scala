package leon
package numerics

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._

import ceres.common.{Rational, RationalInterval}

class Analyser(reporter: Reporter) {
  //class VerificationCondition(val inputs: Map[Expr, RationalInterval], val expr: Expr,
  //val output: RationalInterval, val absRoundoff: Rational) {

  case class PartialInterval(lb: Option[Double], ub: Option[Double]) {
    def isDefined: Boolean = (lb, ub) match {
      case (Some(d1), Some(d2)) => true
      case _ => false
    }

    def checkAndMerge(other: PartialInterval, varName: Variable): PartialInterval = {
      val lwrBnd = this.lb match {
        case Some(v1) => other.lb match {
            case Some(v2) =>
              reporter.error("Found two lower bounds for " + varName)
              None
            case None => this.lb
          }
        case None => other.lb
      }
      val upBnd = this.ub match {
        case Some(v1) => other.ub match {
          case Some(v2) =>
            reporter.error("Found two upper bounds for " + varName)
            None
            case None => this.ub
        }
        case None => other.ub
      }
      PartialInterval(lwrBnd, upBnd)
    }
  }

  val emptyInterval = PartialInterval(None, None)


  def generateVCs(funDef: FunDef): Seq[VerificationCondition] = {
    var vcs: Seq[VerificationCondition] = Seq.empty
  
    val funName = funDef.id.name
    reporter.info("-----> Analysing function " + funName + "...")
    
    val pre = funDef.precondition
    val post = funDef.postcondition
    val body = funDef.body.get

    //Need to check:
    //  - bounds are constraint
    //  - we can handle the body
    //  - we have something to prove
    if (post.isEmpty) {
      reporter.info("no post, nothing to prove")
      Seq.empty
    } else if (pre.isEmpty) {
      reporter.info("no pre, no bounds")
      Seq.empty
    } else {
      val bounds = double2rational(extractVariableBounds(pre.get))
      reporter.info("found variable bounds: " + bounds)
      // TODO: check that all bounds have been defined
      // or maybe postpone till we know what we need.
      val outputRange: Option[RationalInterval] = None
      val rndoff: Option[Rational] = None
      if (outputRange.isEmpty && rndoff.isEmpty) {
        reporter.warning("nothing to prove")
        Seq.empty
      } else {
        // everything seems to be fine
        Seq(VerificationCondition(funDef, bounds, body, outputRange, rndoff))
      }
    }
  }

  // This will need some partial bounds
  // For now only accept bound given as follows:
  // ... && x <= 8.9 && 7.8 <= x && ...
  private def extractVariableBounds(expr: Expr):
    Map[Variable, PartialInterval] = expr match {
    case LessEquals(FloatLiteral(lwrBnd), x @ Variable(name)) =>
      Map(x -> PartialInterval(Some(lwrBnd), None))
    case LessEquals(x @ Variable(name), FloatLiteral(uprBnd)) =>
      Map(x -> PartialInterval(None, Some(uprBnd)))
    case LessEquals(IntLiteral(lwrBnd), x @ Variable(name)) =>
      Map(x -> PartialInterval(Some(lwrBnd), None))
    case LessEquals(x @ Variable(name), IntLiteral(uprBnd)) =>
      Map(x -> PartialInterval(None, Some(uprBnd)))

    case GreaterEquals(FloatLiteral(uprBnd), x @ Variable(name)) =>
      Map(x -> PartialInterval(None, Some(uprBnd)))
    case GreaterEquals(x @ Variable(name), FloatLiteral(lwrBnd)) =>
      Map(x -> PartialInterval(Some(lwrBnd), None))
    case GreaterEquals(IntLiteral(uprBnd), x @ Variable(name)) =>
      Map(x -> PartialInterval(None, Some(uprBnd)))
    case GreaterEquals(x @ Variable(name), IntLiteral(lwrBnd)) =>
      Map(x -> PartialInterval(Some(lwrBnd), None))

    case And(exprs) =>
      var map: Map[Variable, PartialInterval] = Map.empty
      for (e <- exprs) {
        val map2 = extractVariableBounds(e)
        map = map ++ map2.map{ case (k, v) =>
          k -> v.checkAndMerge(map.getOrElse(k, emptyInterval), k)}
      }
      map

    case _ => Map.empty
  }


  private def double2rational(m: Map[Variable, PartialInterval]):
    Map[Variable, RationalInterval] = {
      m.collect { case (k, v) if (v.isDefined) =>
        k -> RationalInterval(Rational(v.lb.get), Rational(v.ub.get))}
  }

  // for now only get one for the resulting expression
  /*def extractAbsRoundoff(expr: Expr): Option[Rational] = expr match {
    case LessEquals(AbsRound)
    return None
  }*/


}
