package leon
package numerics

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._

import ceres.common.{Rational}

class Analyser(reporter: Reporter) {
  val emptyInterval = ParRange(None, None)


  def generateVCs(funDef: FunDef): Seq[VerificationCondition] = {
    var vcs: Seq[VerificationCondition] = Seq.empty
  
    val funName = funDef.id.name
    reporter.info("")
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
      val bounds = extractVariableBounds(pre.get)
      reporter.info("found variable bounds: " + bounds)
      reporter.info("expression to check: " + body)
      reporter.info("precondition: " + pre)
      reporter.info("postcondition: " + post)
      Seq(VerificationCondition(pre.get, body, post.get, funDef, bounds))
    }
  }

  // TODO: issue warning when bound as x < 3.3 ??
  // For now only accept bound given as follows:
  // ... && x <= 8.9 && 7.8 <= x && ...
  private def extractVariableBounds(expr: Expr):
    Map[Variable, ParRange] = expr match {
    case LessEquals(FloatLiteral(lwrBnd), x @ Variable(name)) =>
      Map(x -> ParRange(Some(lwrBnd), None))
    case LessEquals(x @ Variable(name), FloatLiteral(uprBnd)) =>
      Map(x -> ParRange(None, Some(uprBnd)))
    case LessEquals(IntLiteral(lwrBnd), x @ Variable(name)) =>
      Map(x -> ParRange(Some(lwrBnd), None))
    case LessEquals(x @ Variable(name), IntLiteral(uprBnd)) =>
      Map(x -> ParRange(None, Some(uprBnd)))

    case GreaterEquals(FloatLiteral(uprBnd), x @ Variable(name)) =>
      Map(x -> ParRange(None, Some(uprBnd)))
    case GreaterEquals(x @ Variable(name), FloatLiteral(lwrBnd)) =>
      Map(x -> ParRange(Some(lwrBnd), None))
    case GreaterEquals(IntLiteral(uprBnd), x @ Variable(name)) =>
      Map(x -> ParRange(None, Some(uprBnd)))
    case GreaterEquals(x @ Variable(name), IntLiteral(lwrBnd)) =>
      Map(x -> ParRange(Some(lwrBnd), None))

    case And(exprs) =>
      var map: Map[Variable, ParRange] = Map.empty
      for (e <- exprs) {
        val map2 = extractVariableBounds(e)
        map = map ++ map2.map{ case (k, v) =>
          k -> v.checkAndMerge(map.getOrElse(k, emptyInterval), reporter, k)}
      }
      map

    case _ => Map.empty
  }


  /*private def double2rational(m: Map[Variable, ParRange]):
    Map[Variable, RationalInterval] = {
      m.collect { case (k, v) if (v.isDefined) =>
        k -> RationalInterval(Rational(v.lo.get), Rational(v.hi.get))}
  }*/

  // for now only get one for the resulting expression
  /*def extractAbsRoundoff(expr: Expr): Option[Rational] = expr match {
    case LessEquals(AbsRound)
    return None
  }*/


}
