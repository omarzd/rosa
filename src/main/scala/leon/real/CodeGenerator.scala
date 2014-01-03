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
import FPFormat._
import real.Trees._

class CodeGenerator(reporter: Reporter, ctx: LeonContext, options: RealOptions, prog: Program, precision: Precision) {

  val nonRealType: TypeTree = (precision: @unchecked) match {
    case Float64 => Float64Type
    case Float32 => Float32Type
    case DoubleDouble => FloatDDType
    case QuadDouble => FloatQDType
    case _ => Int32Type
  }

  def convertToFloatConstant(e: Option[Expr]) = (e, precision) match {
    case (Some(expr), Float32) =>
      val transformer = new FloatConstantConverter
      Some(transformer.transform(expr))
    case _ => e
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
        Program(programId, ObjectDef(objectId, Seq.empty, Seq.empty))
      }
    case _ => specToFloatCode(programId, objectId, vcs, precision)
  }


  private def specToFloatCode(programId: Identifier, objectId: Identifier, vcs: Seq[VerificationCondition], precision: Precision): Program = {
    var defs: Seq[Definition] = Seq.empty
    val invariants: Seq[Expr] = Seq.empty

    // only generate code for methods that were proven valid.
    // this is not fool-proof, as this check only considers the postcondition check and not the pre-condition checks
    for (vc <- vcs if ( (vc.kind == VCKind.Postcondition || vc.kind == VCKind.SpecGen) && vc.status(precision) == Some(true))) {
      val f = vc.funDef
      val id = f.id
      val floatType = nonRealType
      val args: Seq[VarDecl] = f.args.map(decl => VarDecl(decl.id, floatType))

      val funDef = new FunDef(id, floatType, args)
      funDef.body = convertToFloatConstant(f.body)

      funDef.precondition = f.precondition

      vc.spec(precision) match {
        case specs: Seq[Spec] if (specs.length > 1) =>
          val resId = FreshIdentifier("res").setType(TupleType(Seq(RealType, RealType)))
          val a = FreshIdentifier("a").setType(RealType)
          val b = FreshIdentifier("b").setType(RealType)

          val specExpr = And(specs.map( specToExpr(_) ))

          val resMap: Map[Expr, Expr] = specs.map(s => Variable(s.id)).zip(List(Variable(a), Variable(b))).toMap
          println("resMap: " + resMap)
          println("specExpr: " + specExpr)

          val postExpr = MatchExpr(Variable(resId), 
            Seq(SimpleCase(TuplePattern(None, List(WildcardPattern(Some(a)), WildcardPattern(Some(b)))),
              replace(resMap, specExpr))))

          funDef.postcondition = Some((resId, postExpr))
        case Seq(spec) =>
          val resId = FreshIdentifier("res")
          funDef.postcondition = Some((resId, replace(Map(Variable(spec.id) -> Variable(resId).setType(RealType)), specToExpr(spec))))
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

    val intType = if (bitlength <= 16) Int32Type else Int64Type
    val constConstructor =
      if (bitlength <= 16) (r: Rational, f: Int) => { IntLiteral(rationalToInt(r, f)) }
      else (r: Rational, f: Int) => { LongLiteral(rationalToLong(r, f)) }

    val solver = new RealSolver(ctx, prog, options.z3Timeout)

    for (vc <- vcs if (vc.kind == VCKind.Postcondition || vc.kind == VCKind.SpecGen)) {
      val f = vc.funDef
      val id = f.id
      val args = f.args.map(decl => VarDecl(decl.id, intType))
      val funDef = new FunDef(id, intType, args)

      println("\n ==== \nfnc id: " + id)
      println("vc.kind " + vc.kind)
      println("generating code for: " + vc.body)

      // convert to SSA form, then run through Approximator to get ranges of all intermediate variables
      val ssaBody = idealToActual(toSSA(vc.body), vc.variables)
      val transformer = new Approximator(reporter, solver, precision, vc.pre, vc.variables)
      val (newBody, newSpec) = transformer.transformWithSpec(ssaBody, false)

      val formats = transformer.variables.map {
        case (v, r) => (v, FPFormat.getFormat(r.interval.xlo, r.interval.xhi, bitlength))
      }
      println("formats: " + formats)
      println("ssaBody: " + ssaBody)


      val fpBody = translateToFP(ssaBody, formats, bitlength, constConstructor)

      funDef.body = Some(mathToCode(actualToIdealVars(fpBody, vc.variables)))

      defs = defs :+ funDef
    }

    val newProgram = Program(programId, ObjectDef(objectId, defs, invariants))
    newProgram
  }

  // TODO: fp translation with if-then-else and function calls
  private def mathToCode(expr: Expr): Expr = expr match {
    case And(args) => Block(args.init.map(a => mathToCode(a)), mathToCode(args.last))
    case Equals(Variable(id), rhs) => ValAssignment(id, rhs)
    case _ => expr
  }


}
