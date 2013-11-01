/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Common._
import purescala.TypeTrees._
import xlang.Trees.Block

import real.TreeOps._
import real.{FixedPointFormat => FPFormat}
import real.Trees._

class CodeGenerator(reporter: Reporter, ctx: LeonContext, options: RealOptions, prog: Program, precision: Precision) {

  val nonRealType: TypeTree = (precision: @unchecked) match {
    case Float64 => Float64Type
    case Float32 => Float32Type
    case DoubleDouble => FloatDDType
    case QuadDouble => FloatQDType
    case _ => Int32Type
  }

  def specToCode(programId: Identifier, objectId: Identifier, vcs: Seq[VerificationCondition]): Program = precision match {
    case FPPrecision(bts) => specToFixedCode(programId, objectId, vcs, bts)
    case _ => specToFloatCode(programId, objectId, vcs, precision)
  }


  private def specToFloatCode(programId: Identifier, objectId: Identifier, vcs: Seq[VerificationCondition], precision: Precision): Program = {
    var defs: Seq[Definition] = Seq.empty
    val invariants: Seq[Expr] = Seq.empty

    for (vc <- vcs) {
      val f = vc.funDef
      val id = f.id
      val floatType = nonRealType
      val returnType = floatType // FIXME: check that this is actually RealType
      val args: Seq[VarDecl] = f.args.map(decl => VarDecl(decl.id, floatType))

      val funDef = new FunDef(id, returnType, args)
      funDef.body = f.body

      funDef.precondition = f.precondition

      vc.spec(precision) match {
        case Some(spec) =>
          val resId = FreshIdentifier("res")
          funDef.postcondition = Some((resId, replace(Map(ResultVariable() -> Variable(resId).setType(RealType)), specToExpr(spec))))
        case _ =>
      }

      defs = defs :+ funDef
    }

    val newProgram = Program(programId, ObjectDef(objectId, defs, invariants))
    newProgram
  }

  // This is repeating some of the computation
  private def specToFixedCode(programId: Identifier, objectId: Identifier, vcs: Seq[VerificationCondition], bitlength: Int): Program = {
    var defs: Seq[Definition] = Seq.empty
    val invariants: Seq[Expr] = Seq.empty

    val solver = new RealSolver(ctx, prog, options.z3Timeout)

    for (vc <- vcs) {
      val f = vc.funDef
      val id = f.id
      val args: Seq[VarDecl] = f.args.map(decl => VarDecl(decl.id, Int32Type))
      val funDef = new FunDef(id, Int32Type, args)
      
      // convert to SSA form, then run through FloatApproximator to get ranges of all intermediate variables
      val ssaBody = idealToActual(toSSA(vc.body), vc.variables)
      val transformer = new FloatApproximator(reporter, solver, precision, vc.pre, vc.variables)
      val (newBody, newSpec) = transformer.transformWithSpec(ssaBody)
      
      val formats = transformer.variables.map {
        case (v, r) => (v, FPFormat.getFormat(r.interval.xlo, r.interval.xhi, bitlength))
      }
      val fpBody = translateToFP(ssaBody, formats, bitlength)
      
      funDef.body = Some(actualToIdealVars(removeResAssignment(andToBlocks(fpBody)), vc.variables))

      defs = defs :+ funDef
    }

    val newProgram = Program(programId, ObjectDef(objectId, defs, invariants))
    newProgram
  }

  // TODO: fp translation with if-then-else and function calls
  def andToBlocks(expr: Expr): Expr = expr match {
    case And(args) => Block(args.init.map(a => andToBlocks(a)), andToBlocks(args.last))
    case _ => expr
  }

  def removeResAssignment(expr: Expr): Expr = expr match {
    case Block(es, last) => Block(es, removeResAssignment(last))
    case Equals(FResVariable(), e) => e
  }

  

  
}