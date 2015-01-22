/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package real

import purescala.Trees._
import real.Trees._
import purescala.TreeOps.{replace}
import real.TreeOps._
import VariableShop._
import purescala.Definitions._
import real.{FixedPointFormat => FPFormat}
import FPFormat._
import purescala.TransformerWithPC

trait FixedpointCodeGenerator {

  val reporter: Reporter

  val constConstructorInt = (r: Rational, f: Int) => { IntLiteral(rationalToInt(r, f)) }
      
  val constConstructorLong = (r: Rational, f: Int) => { LongLiteral(rationalToLong(r, f)) }

  /*
    Turns the VC body into fixed-point code.
    @return (fixed-point body, number of fractional bits of the result)
  */
  def getFPCode(vc: VerificationCondition, solver: RangeSolver, bitlength: Int, fncs: Map[FunDef, Fnc]): (Expr, Int) = {
    
    // if we have loops, we cannot inline the body, but if it's straightline code, we get more precise results.
    // TODO: this should be done based on which verification succeeded...
    val body = if (vc.kind == VCKind.LoopPost) vc.inlinedBody.get else vc.body

    val ssaBody = addResultsF(idealToActual(toSSA(body, fncs), vc.variables), vc.variables.fResultVars)

    val transformer = new AAApproximator(reporter, solver, FPPrecision(bitlength), true, checkPathError = false, collectIntervals = true)
    val approxVariables = transformer.approximateEquations(ssaBody, vc.pre, vc.variables, exactInputs = false)
    val tmpIntervals = transformer.fpIntervals ++ approxVariables.map(x => (x._1 -> x._2.interval))
         
    val formats = tmpIntervals.map {
      case (v, i) => (v, FPFormat.getFormat(i.xlo, i.xhi, bitlength))
    }
    //println("formats: " + formats); //println("ssaBody: " + ssaBody)
    val fpBody = translateToFP(ssaBody, formats, bitlength,
       if (bitlength <= 16) constConstructorInt else constConstructorLong)

    var resFracBits = formats(vc.variables.fResultVars.head).f

    (actualToIdealVars(fpBody, vc.variables), resFracBits)
  }

  def toSSA(expr: Expr, fncs: Map[FunDef, Fnc]): Expr = {
    //println("transforming to SSA: " + expr)

    val transformer = new SSATransformer(fncs)
    transformer.transform(expr)
  }

  private class SSATransformer(fncs: Map[FunDef, Fnc]) extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    // Note that this transforms real arithmetic to float arithmetic
    private def arithToSSA(expr: Expr): (Seq[Expr], Expr) = expr match {
      case PlusR(lhs, rhs) =>
        val (lSeq, lVar) = arithToSSA(lhs)
        val (rSeq, rVar) = arithToSSA(rhs)
        val tmpVar = getFreshValidTmp
        (lSeq ++ rSeq :+ Equals(tmpVar, PlusR(lVar, rVar)), tmpVar)

      case MinusR(lhs, rhs) =>
        val (lSeq, lVar) = arithToSSA(lhs)
        val (rSeq, rVar) = arithToSSA(rhs)
        val tmpVar = getFreshValidTmp
        (lSeq ++ rSeq :+ Equals(tmpVar, MinusR(lVar, rVar)), tmpVar)

      case TimesR(lhs, rhs) =>
        val (lSeq, lVar) = arithToSSA(lhs)
        val (rSeq, rVar) = arithToSSA(rhs)
        val tmpVar = getFreshValidTmp
        (lSeq ++ rSeq :+ Equals(tmpVar, TimesR(lVar, rVar)), tmpVar)

      case DivisionR(lhs, rhs) =>
        val (lSeq, lVar) = arithToSSA(lhs)
        val (rSeq, rVar) = arithToSSA(rhs)
        val tmpVar = getFreshValidTmp
        (lSeq ++ rSeq :+ Equals(tmpVar, DivisionR(lVar, rVar)), tmpVar)

      case UMinusR(t) =>
        val (seq, v) = arithToSSA(t)
        val tmpVar = getFreshValidTmp
        (seq :+ Equals(tmpVar, UMinusR(v)), tmpVar)

      case RealLiteral(_) | Variable(_)  | IntLiteral(_) => (Seq[Expr](), expr)

      // function value for recursive functions
      case FncValue(specs, specExpr, model, _, _) =>
        if (specs.length == 1) {
          val tmpVar = getFreshValidTmp
          (Seq[Expr]() :+ Equals(tmpVar, expr), tmpVar)
        } else {
          val tmpVars: Seq[Expr] = specs.map(s => getFreshValidTmp)
          (Seq[Expr]() :+ Equals(Tuple(tmpVars), expr), Tuple(tmpVars))
        }

      /*case FunctionInvocation(funDef, args) =>
        val argsToSSA: Seq[(Seq[Expr], Expr)] = args.map( arithToSSA(_) )

        println("argsToSSA: " + argsToSSA)
        val (ssa, newArgs) = argsToSSA.unzip
        //val arguments: Map[Expr, Expr] = funDef.fd.params.map(decl => decl.toVariable).zip(newArgs).toMap

        val tmpVar = getFreshValidTmp
        (ssa.flatten :+ Equals(tmpVar, FunctionInvocation(funDef, newArgs)), tmpVar)
      */
      case FunctionInvocation(funDef, args) =>
        val argsToSSA: Seq[(Seq[Expr], Expr)] = args.map( arithToSSA(_) )

        //println("argsToSSA: " + argsToSSA)
        val (ssa, newArgs) = argsToSSA.unzip

        val arguments: Map[Expr, Expr] = funDef.fd.params.map(decl => decl.toVariable).zip(newArgs).toMap
      //  println("functions: " + fncs)
      //  println("exprs: " + expr)
        val fncBody = fncs(funDef.fd).body


        val newBody = replace(arguments, fncBody)
        
        val tmpVar = getFreshValidTmp
        (ssa.flatten :+ Equals(tmpVar, FncBody(funDef.id.name, newBody, funDef.fd, newArgs)), tmpVar)
      
    }

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case Equals(v, arithExpr: RealArithmetic) =>
        val (seq, tmpVar) = arithToSSA(arithExpr)
        And(And(seq), EqualsF(v, tmpVar))

      case Equals(v, fnc: FunctionInvocation) =>
        val (seq, tmpVar) = arithToSSA(fnc)
        And(And(seq), EqualsF(v, tmpVar))
      
      case IfExpr(GreaterEquals(l, r), t, e) =>
        val (seqLhs, tmpVarLhs) = arithToSSA(l)
        val (seqRhs, tmpVarRhs) = arithToSSA(r)
        And(And(seqLhs ++ seqRhs), IfExpr(GreaterEquals(tmpVarLhs, tmpVarRhs), rec(t, path), rec(e, path)))

      case IfExpr(LessEquals(l, r), t, e) =>
        val (seqLhs, tmpVarLhs) = arithToSSA(l)
        val (seqRhs, tmpVarRhs) = arithToSSA(r)
        And(And(seqLhs ++ seqRhs), IfExpr(LessEquals(tmpVarLhs, tmpVarRhs), rec(t, path), rec(e, path)))

      case IfExpr(GreaterThan(l, r), t, e) =>
        val (seqLhs, tmpVarLhs) = arithToSSA(l)
        val (seqRhs, tmpVarRhs) = arithToSSA(r)
        And(And(seqLhs ++ seqRhs), IfExpr(GreaterThan(tmpVarLhs, tmpVarRhs), rec(t, path), rec(e, path)))

      case IfExpr(LessThan(l, r), t, e) =>
        val (seqLhs, tmpVarLhs) = arithToSSA(l)
        val (seqRhs, tmpVarRhs) = arithToSSA(r)
        And(And(seqLhs ++ seqRhs), IfExpr(LessThan(tmpVarLhs, tmpVarRhs), rec(t, path), rec(e, path)))

      case arithExpr: RealArithmetic =>
        val (seq, tmpVar) = arithToSSA(arithExpr)
        And(And(seq), tmpVar)

      case fnc: FunctionInvocation =>
        val (seq, tmpVar) = arithToSSA(fnc)
        And(And(seq), tmpVar)

      case fnc: FncValue =>
        val (seq, tmpVar) = arithToSSA(fnc)
        And(And(seq), tmpVar)      

      case _ =>
        //println("!!!  other: " + e)
        super.rec(e, path)
    }
  }

}