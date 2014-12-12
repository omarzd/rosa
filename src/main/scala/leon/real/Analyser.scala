/* Copyright 2013-2014 EPFL, Lausanne */

package leon
package real

import purescala.Common._
import purescala.Definitions.{FunDef}
import purescala.Trees._
import purescala.TypeTrees.{RealType, BooleanType}
import purescala.TreeOps.replace
import purescala.TreeOps.functionCallsOf
import purescala.TransformerWithPC

import real.Trees.{Roundoff, Iteration, UpdateFunction, Assertion, InitialErrors}
import real.TreeOps._
import real.VariableShop._
import purescala.TreeOps._

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
    val (complete, incomplete) = sortedFncs.partition(f => {
      reporter.debug(f.id.name + ": precond.: " + f.precondition)
      f.body.isDefined && f.precondition.nonEmpty
      })

    
    incomplete.foreach(f =>
      if (f.annotations.contains("model")) {
        f.postcondition match {
          case Some((resId, postExpr)) =>
            assert(f.returnType == RealType)
            val resFresh = FreshIdentifier("result", true).setType(RealType)
            val postcondition = extractPostCondition(resId, postExpr, Seq(resFresh) )
            fncs += ((f -> Fnc(True, f.body.get, postcondition)))
          case _ => 
            reporter.warning(f.id.name + ": marked as model but no postcondition found.")
        }
      } else {
        reporter.warning(f.id.name + ": body or precondition empty, skipping")
      })

    val (validFncs, invalidInputs) = complete.map(
      funDef => {
        (funDef, VariablePool(funDef.precondition.get, funDef.params, funDef.returnType))
      }).partition( x => x._2.nonEmpty)
    invalidInputs.foreach(x => reporter.warning(x._1.id.name + ": inputs incomplete, skipping!"))

    for ((funDef, Some(variables)) <- validFncs) {
      val preGiven = removeInitialErrors( funDef.precondition.get )
      debug ("precondition is acceptable")
      val allFncCalls = functionCallsOf(funDef.body.get).map(invc => invc.tfd.id.toString)

      debug("variables: " + variables)

      // Add default roundoff on inputs
      val precondition = And(preGiven, And(variables.inputsWithoutNoiseAndNoInt.map(i => Roundoff(i))))
      debug ("precondition: " + precondition)

      val resFresh = variables.resIds
      val body = letsToEquals(funDef.body.get)
      debug("body: " + body)

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
          
          val assertionCollector = new AssertionCollector(funDef, precondition, variables, precisions)
          assertionCollector.transform(body)

          val bodyVCKind = if (assertionCollector.recursive) LoopPost else Postcondition
          val vcBody = new VerificationCondition(funDef, bodyVCKind, precondition, body, postcondition,
            allFncCalls, variables, precisions)

          vcs ++= assertionCollector.vcs :+ vcBody
          // for function inlining
          fncs += ((funDef -> Fnc(precondition, body, postcondition)))
         
        case None => // only want to generate specs
          val vcBody = new VerificationCondition(funDef, SpecGen, precondition, body, True,
            allFncCalls, variables, precisions)

          vcs ++= Seq(vcBody)
          fncs += ((funDef -> Fnc(precondition, body, True)))
      }
    }
    val sorted = vcs.sortWith((vc1, vc2) => lt(vc1, vc2))
    reporter.debug("VCs:")
    sorted.foreach(vc => reporter.debug(vc.longString))
    (sorted, fncs)
  }

  def removeInitialErrors(e: Expr): Expr = {
    preMap {
      case InitialErrors(_) => Some(True)
      case _ => None
    }(e)
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


  // TODO: ignoring body for now
  private def unroll(body: Seq[Expr], updates: Seq[UpdateFunction], max: Int, varMap: Map[Expr, Expr],
    unrolled: Seq[Expr], count: Int): Seq[Expr] = {
    
    if (count >= max) {
      val newUpdates = updates.map({
        case UpdateFunction(lhs, rhs) =>
          replace(varMap, rhs)
        })


      if (updates.length > 1) { unrolled :+ Tuple(newUpdates) }
      else { unrolled :+ newUpdates.head }
    } else {
      //println("loop " + count)
      //println("varMap: " + varMap)
      var newVarMap: Map[Expr, Expr] = Map.empty
      val newUpdates = updates.map({
        case UpdateFunction(lhs, rhs) =>
          val newVal = Variable(FreshIdentifier(lhs.toString + count)).setType(RealType)
          newVarMap += ((lhs -> newVal))
          Equals(newVal, replace(varMap, rhs))
        })
      //println("newUpdates: " + newUpdates)
      //println("newVarMap: " + newVarMap)
      //val newLoop = body  

      unroll(body, updates, max, newVarMap, unrolled ++ newUpdates, count + 1)
    }


  }

  class AssertionCollector(outerFunDef: FunDef, precondition: Expr, variables: VariablePool, precisions: List[Precision]) extends TransformerWithPC {
    def isConstraint(e: Expr): Boolean = e match {
      case LessThan(_,_) | LessEquals(_,_) | GreaterThan(_,_) | GreaterEquals(_,_) => true
      case Not(_) => true
      case _ => false
    }

    def extractLoopBound(e: Expr): Int = e match {
      case And(args) => extractLoopBound(args.head) // has to be the first statement
      case LessThan(v @ Variable(id), IntLiteral(b)) => b
      case _ =>
        throw new Exception("Unknown loop format!")
        0
    }

    type C = Seq[Expr]
    val initC = Nil

    var vcs = Seq[VerificationCondition]()
    var recursive = false

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case FunctionInvocation(funDef, args) if (funDef.precondition.isDefined) =>

        val (simpleArgs, morePath) = args.map(a => a match {
          case Variable(_) => (a, True)
          case _ =>
            val fresh = getFreshTmp
            (fresh, Equals(fresh, a))
        }).unzip

        val pathToFncCall = And(path ++ morePath)
        
        val arguments: Map[Expr, Expr] = funDef.params.map(decl => decl.toVariable).zip(simpleArgs).toMap
        
        val toProve = replace(arguments, removeInitialErrors(removeRoundoff(funDef.precondition.get)) )
        

        val allFncCalls = functionCallsOf(pathToFncCall).map(invc => invc.tfd.id.toString)
        if (outerFunDef.id == funDef.id) {
          recursive = true

          val lowerLoopBound: Int = variables.inputs.get(Variable(variables.loopCounter.get)) match {
            case Some(rec) => rec.lo.toInt
            case None => 0
          }
          val loopBound = Some(extractLoopBound(pathToFncCall) - lowerLoopBound)
          //println("loopBound: " + loopBound)
          
          val (constrs, computation) = getClauses(pathToFncCall).partition(x => isConstraint(x))
          //println("pathToFncCall: " + pathToFncCall)
          //println("computation: " + computation)
          
          val vc = new VerificationCondition(outerFunDef, LoopInvariant, And(precondition, And(constrs)),
           And(computation), toProve, allFncCalls, variables, precisions)
          //vc.updateFunctions = updateFncs.toSeq
          vc.updateFunctions = arguments.filter(x => !variables.isLoopCounter(x._1) &&
            !variables.isInteger(x._1)).map({
              case (Variable(id), upfnc) => (id, upfnc)
              }).toSeq
          //println("updateFunctions: " + vc.updateFunctions)

          vc.loopBound = loopBound

          vcs :+= vc
        } else {
          //(Precondition, Seq[UpdateFunction]())

          vcs :+= new VerificationCondition(outerFunDef, Precondition, precondition, pathToFncCall, toProve,
            allFncCalls, variables, precisions)
        }

        e

      case Assertion(toProve) =>
        val pathToAssertion = And(path)
        val allFncCalls = functionCallsOf(pathToAssertion).map(invc => invc.tfd.id.toString)
        vcs :+= new VerificationCondition(outerFunDef, VCKind.Assert, precondition, pathToAssertion, toProve, allFncCalls, variables, precisions)
        e
      case _ =>
        super.rec(e, path)
    }
  }

}