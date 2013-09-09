/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Definitions._
import purescala.Trees._
import purescala.Common._
import purescala.TypeTrees._

import real.TreeOps._

object CodeGenerator {

  def specToCode(programId: Identifier, objectId: Identifier, vcs: Seq[VerificationCondition], precision: Precision): Program = precision match {
    case FPPrecision(bts) => specToFixedCode(programId, objectId, vcs, precision)
    case _ => specToFloatCode(programId, objectId, vcs, precision)
  }


  private def getNonRealType(precision: Precision): TypeTree = precision match {
    case Float64 => Float64Type
    case Float32 => Float32Type
    case DoubleDouble => FloatDDType
    case QuadDouble => FloatQDType
  }



  def specToFloatCode(programId: Identifier, objectId: Identifier, vcs: Seq[VerificationCondition], precision: Precision): Program = {
    var defs: Seq[Definition] = Seq.empty

    for (vc <- vcs) {
      val f = vc.funDef
      val id = f.id
      val floatType = getNonRealType(precision)
      val returnType = floatType // FIXME: check that this is actually RealType
      val args: Seq[VarDecl] = f.args.map(decl => VarDecl(decl.id, floatType))

      val funDef = new FunDef(id, returnType, args)
      funDef.body = f.body

      funDef.precondition = f.precondition

      vc.spec(precision) match {
        case Some(spec) => funDef.postcondition = Some(specToExpr(spec))
        case _ =>
      }

      defs = defs :+ funDef
    }
    val invariants: Seq[Expr] = Seq.empty

    val newProgram = Program(programId, ObjectDef(objectId, defs, invariants))
    newProgram
  }


  def specToFixedCode(programId: Identifier, objectId: Identifier, vcs: Seq[VerificationCondition], precision: Precision): Program = {
    var defs: Seq[Definition] = Seq.empty
    val invariants: Seq[Expr] = Seq.empty
    // TODO
    val newProgram = Program(programId, ObjectDef(objectId, defs, invariants))
    newProgram
  }
}