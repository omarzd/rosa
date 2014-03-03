/* Copyright 2013-2014 EPFL, Lausanne */

package leon
package real

//import purescala.Common._
import purescala.Definitions.{FunDef}
import purescala.Trees._
import purescala.TreeOps.replace
import purescala.TreeOps.functionCallsOf

import real.Trees.{Roundoff, Iteration, UpdateFunction}
import real.TreeOps._

import VCKind._

object Analyser {
  implicit val debugSection = utils.DebugSectionReals
  
  def analyzeThis(sortedFncs: Seq[FunDef], precisions: List[Precision], reporter: Reporter): (Seq[VerificationCondition], Map[FunDef, Fnc]) = {
    def debug(msg: String): Unit = {
      reporter.debug(msg)
    }

    var vcs = Seq[VerificationCondition]()
    var fncs = Map[FunDef, Fnc]()

    // completeness of specs checks
    val (complete, incomplete) = sortedFncs.partition(f =>  f.body.isDefined && f.precondition.nonEmpty)
    incomplete.foreach(f => reporter.warning(f.id.name + ": body or precondition empty, skipping"))
    val (validFncs, invalidInputs) = complete.map(
      funDef => {
        val variables = VariablePool(funDef.precondition.get, funDef.returnType)
        (funDef, variables)
      }).partition( x => x._2.hasValidInput(x._1.params, reporter))
    invalidInputs.foreach(x => reporter.warning(x._1.id.name + ": inputs incomplete, skipping!"))

    for ((funDef, variables) <- validFncs) {
      val preGiven = funDef.precondition.get
      debug ("precondition is acceptable")
      val allFncCalls = functionCallsOf(funDef.body.get).map(invc => invc.tfd.id.toString)

      // Add default roundoff on inputs
      val precondition = And(preGiven, And(variables.inputsWithoutNoise.map(i => Roundoff(i))))
      debug ("precondition: " + precondition)

      val resFresh = variables.resIds
      val body = letsToEquals(funDef.body.get)
      debug("body: " + body)

      if (containsIteration(body)) {
        (body, funDef.postcondition) match {
          case (Iteration(ids, lb, upFncs), Some((resId, postExpr))) =>
            
            val loopInv = simplifyConstraint(And(preGiven, extractPostCondition(resId, postExpr, ids)))
            
            debug (s"loopInv: $loopInv")
            
            val loopInvAfterLoop = replace(ids.zip(resFresh).map({ 
                case (id, r) => (Variable(id) -> Variable(r))
              }).toMap, loopInv)
            debug (s"loopInvAfterLoop: $loopInvAfterLoop")
            
            /*val updates = resFresh.zip(upFncs).map({
              case (res, UpdateFunction(Variable(id), rhs)) =>
                Equals(Variable(res), rhs)
              })*/
            val update = Tuple(upFncs.map(uf => uf.asInstanceOf[UpdateFunction].rhs))
              
            val loopBody = And(Seq(lb) :+ update)
            debug (s"loopBody: $loopBody")

            val vc = new VerificationCondition(funDef, LoopInvariant, loopInv, loopBody, loopInvAfterLoop,
              allFncCalls, variables, precisions)

            //println("\nfinal VC: \n" + vc.longString)

            val vcError = new VerificationCondition(funDef, LoopError, preGiven, body, False,
              allFncCalls, variables, precisions)
            //println("\nfinal VC error \n" + vcError.longString)

            vcs ++= Seq(vc, vcError)
            // TODO: include recursive functions in overall functions
            //fncs += ((funDef -> Fnc() ))

          // Error computation only
          case (_, None) =>
            // TODO

        }  
      } else {
      funDef.postcondition match {
         //Option[(Identifier, Expr)]
         // TODO: invariants
         /*case Some((ResultVariable()) =>
           val posts = getInvariantCondition(funDef.body.get)
           val bodyWOLets = convertLetsToEquals(funDef.body.get)
           val body = replace(posts.map(p => (p, True)).toMap, bodyWOLets)
           (body, body, Or(posts))*/

        case Some((resId, postExpr)) =>
          val postcondition = extractPostCondition(resId, postExpr, resFresh)

          val vcBody = new VerificationCondition(funDef, Postcondition, precondition, body, postcondition,
            allFncCalls, variables, precisions)

          val assertionCollector = new AssertionCollector(funDef, precondition, variables, precisions)
          assertionCollector.transform(body)

          vcs ++= assertionCollector.vcs :+ vcBody
          // for function inlining
          fncs += ((funDef -> Fnc(precondition, body, postcondition)))
         
        case None => // only want to generate specs
          val vcBody = new VerificationCondition(funDef, SpecGen, precondition, body, True,
            allFncCalls, variables, precisions)

          vcs ++= Seq(vcBody)
          fncs += ((funDef -> Fnc(precondition, body, True)))
      }}
    }

    (vcs.sortWith((vc1, vc2) => lt(vc1, vc2)), fncs)
  }

  // can return several, as we may have an if-statement
  private def getInvariantCondition(expr: Expr): List[Expr] = expr match {
    case IfExpr(cond, thenn, elze) => getInvariantCondition(thenn) ++ getInvariantCondition(elze)
    case Let(binder, value, body) => getInvariantCondition(body)
    case LessEquals(_, _) | LessThan(_, _) | GreaterThan(_, _) | GreaterEquals(_, _) => List(expr)
    case Equals(_, _) => List(expr)
    case _ =>
      println("!!! Expected invariant, but found: " + expr.getClass)
      List(BooleanLiteral(false))
  }

  private def lt(vc1: VerificationCondition, vc2: VerificationCondition): Boolean = {
    if (vc1.allFncCalls.isEmpty) vc1.fncId < vc2.fncId
    else if (vc1.allFncCalls.contains(vc2.fncId)) false
    else true //vc1.fncId < vc2.fncId
  }

  /*
  class AssertionRemover extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case Assertion(expr) => True
      case _ =>
        super.rec(e, path)
    }
  }*/
}