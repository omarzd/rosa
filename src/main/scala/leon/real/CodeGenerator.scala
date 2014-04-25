/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.TransformerWithPC
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Common._
import purescala.TypeTrees._
import xlang.Trees.Block

import real.TreeOps._
import real.{FixedPointFormat => FPFormat}
import FPFormat._
import real.Trees._
import VariableShop._


object CodeGenerator {

  val constConstructorInt = (r: Rational, f: Int) => { IntLiteral(rationalToInt(r, f)) }
      
  val constConstructorLong = (r: Rational, f: Int) => { LongLiteral(rationalToLong(r, f)) }

  /*
    Turns the VC body into fixed-point code.
    @return (fixed-point body, number of fractional bits of the result)
  */
  def getFPCode(vc: VerificationCondition, solver: RangeSolver, bitlength: Int, fncs: Map[FunDef, Fnc],
    reporter: Reporter): (Expr, Int) = {
    
    val ssaBody = idealToActual(toSSA(vc.body, fncs), vc.variables)
    val transformer = new AAApproximator(reporter, solver, FPPrecision(bitlength), checkPathError = false)
    val approxVariables = transformer.approximateEquations(ssaBody, vc.pre, vc.variables, exactInputs = false)
         
    val formats = approxVariables.map {
      case (v, r) => (v, FPFormat.getFormat(r.interval.xlo, r.interval.xhi, bitlength))
    }
    //println("formats: " + formats); println("ssaBody: " + ssaBody)
    val fpBody = translateToFP(ssaBody, formats, bitlength,
       if (bitlength <= 16) constConstructorInt else constConstructorLong)

    var resFracBits = formats(vc.variables.fResultVars.head).f

    (actualToIdealVars(fpBody, vc.variables), resFracBits)
  }

  def toSSA(expr: Expr, fncs: Map[FunDef, Fnc]): Expr = {
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

      case RealLiteral(_) | Variable(_) => (Seq[Expr](), expr)

      case FunctionInvocation(funDef, args) =>
        val argsToSSA: Seq[(Seq[Expr], Expr)] = args.map( arithToSSA(_) )

        val (ssa, newArgs) = argsToSSA.unzip

        val arguments: Map[Expr, Expr] = funDef.fd.params.map(decl => decl.toVariable).zip(newArgs).toMap
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

      case _ =>
        super.rec(e, path)
    }
  }

}

class CodeGenerator(reporter: Reporter, ctx: LeonContext, options: RealOptions, prog: Program, precision: Precision, fncs: Map[FunDef, Fnc]) {
  import CodeGenerator._

  val nonRealType: TypeTree = (precision: @unchecked) match {
    case Float64 => Float64Type
    case Float32 => Float32Type
    case DoubleDouble => FloatDDType
    case QuadDouble => FloatQDType
    case _ => Int32Type
  }

  def getReturnType(realType: TypeTree): TypeTree = realType match {
    case TupleType(args) => TupleType(args.map(a => getReturnType(a)))
    case simpleType => nonRealType
  }

  def convertToFloatConstant(e: Option[Expr]) = (e, precision) match {
    case (Some(expr), Float32) =>
      val transformer = new FloatConstantConverter

      val tmp = transformer.transform(expr)
      val tmp2 = convertConstants(expr)
      assert(tmp == tmp2)

      Some(tmp)
    case _ => e
  }

  def convertConstants(e: Expr): Expr = {
    preMap {
      case r: RealLiteral => r.floatType = true; Some(r)
      case _ => None
    }(e)
  }

  class FloatConstantConverter extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case r: RealLiteral => r.floatType = true; r
      case _ =>
          super.rec(e, path)
    }
  }

  def specToCode(programId: Identifier, objectId: Identifier, vcs: Seq[VerificationCondition]): Program = precision match {
    case FPPrecision(bts) =>
      if (bts <= 32) specToFixedCode(programId, objectId, vcs, bts)
      else {
        reporter.error("Fixed-point code generation not possible for bitlengths larger than 32 bits.")
        Program(programId, List())
      }
    case _ => specToFloatCode(programId, objectId, vcs, precision)
  }


  private def specToFloatCode(programId: Identifier, objectId: Identifier, vcs: Seq[VerificationCondition], precision: Precision): Program = {
    var defs: Seq[Definition] = Seq.empty
    
    for (vc <- vcs if (vc.kind == VCKind.Postcondition || vc.kind == VCKind.SpecGen || vc.kind == VCKind.LoopInvariant)) {
      val f = vc.funDef
      val id = f.id
      val floatType = nonRealType
      val args: Seq[ValDef] = f.params.map(decl => ValDef(decl.id, floatType))
      val returnType = getReturnType(vc.funDef.returnType)

      //val funDef = new FunDef(id, Seq.empty, floatType, args)
      //funDef.body = convertToFloatConstant(f.body)
      val funDef = /*if(vc.kind == VCKind.LoopInvariant) {
        val counterId = FreshIdentifier("_counter").setType(Int32Type)
        val maxCounterId = FreshIdentifier("_MAX_COUNTER").setType(Int32Type)

        val fD = new FunDef(id, Seq.empty, returnType, args :+ ValDef(counterId, Int32Type) :+ ValDef(maxCounterId, Int32Type))
        val loopBody = convertToFloatConstant(f.body)
        
        fD.body =  loopBody.get match {
          case Iteration(ids, bd, upFncs) =>
            val cond = LessThan(Variable(counterId), Variable(maxCounterId))

            val thenn = Block(if (bd == True) Seq.empty else Seq(bd),
              FunctionInvocation(TypedFunDef(fD, Seq.empty),
                upFncs.asInstanceOf[Seq[UpdateFunction]].map(uf => uf.rhs)))

            val elze = Tuple(ids.map(i => Variable(i)))

            Some(IfExpr(cond, thenn, elze))

            /*if (counter < MAXCOUNTER) {
              body
              fncCall(upFncs)
            } else {
              (ids)
            }*/

          case _ => throw new Exception("Unsupported loop! Don't know how to generate.")
        }

         
        fD
      } else {*/
      {  val fD = new FunDef(id, Seq.empty, returnType, args)
        fD.body = convertToFloatConstant(f.body)

        vc.spec(precision) match {
          case specs: Seq[Spec] if (specs.length > 1) =>
            val resId = FreshIdentifier("res").setType(TupleType(Seq(RealType, RealType)))
            val a = FreshIdentifier("a").setType(RealType)
            val b = FreshIdentifier("b").setType(RealType)

            val specExpr = And(specs.map( _.toExpr ))

            val resMap: Map[Expr, Expr] = specs.map(s => Variable(s.id)).zip(List(Variable(a), Variable(b))).toMap
            
            val postExpr = MatchExpr(Variable(resId), 
              Seq(SimpleCase(TuplePattern(None, List(WildcardPattern(Some(a)), WildcardPattern(Some(b)))),
                replace(resMap, specExpr))))

            fD.postcondition = Some((resId, postExpr))
          case Seq(spec) =>
            val resId = FreshIdentifier("res")
            fD.postcondition = Some((resId, replace(Map(Variable(spec.id) -> Variable(resId).setType(RealType)), spec.toExpr)))
          case _ =>
        }
        fD
      }

      
      funDef.precondition = f.precondition


      

      defs = defs :+ funDef
    }

    val newProgram = Program(programId, List(ModuleDef(objectId, defs)))
    newProgram
  }

  // This is repeating some of the computation
  private def specToFixedCode(programId: Identifier, objectId: Identifier, vcs: Seq[VerificationCondition], bitlength: Int): Program = {
    var defs: Seq[Definition] = Seq.empty
    val invariants: Seq[Expr] = Seq.empty

    val intType = if (bitlength <= 16) Int32Type else Int64Type
    
    val solver = new RangeSolver(options.z3Timeout)    

    for (vc <- vcs if (vc.kind == VCKind.Postcondition || vc.kind == VCKind.SpecGen)) {
      val f = vc.funDef
      val id = f.id
      val args = f.params.map(decl => ValDef(decl.id, intType))
      val funDef = new FunDef(id, Seq.empty, intType, args)

      val fpBody = getFPCode(vc, solver, bitlength, fncs, reporter)._1

      funDef.body = Some(mathToCode(fpBody))
      defs = defs :+ funDef
    }

    val newProgram = Program(programId, List(ModuleDef(objectId, defs)))
    newProgram
  }

  private def mathToCode(expr: Expr): Expr = expr match {
    case And(args) => Block(args.init.map(a => mathToCode(a)), mathToCode(args.last))
    case Equals(Variable(id), rhs) => ValAssignment(id, rhs)
    case IfExpr(c, t, e) => IfExpr(c, mathToCode(t), mathToCode(e))
    case _ => expr
  }
}
