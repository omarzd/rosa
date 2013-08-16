/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import Precision._

class CodeGeneration(reporter: Reporter, precision: Precision) {
  /*val specTransformer = new SpecTransformer

  def specToCode(programId: Identifier, objectId: Identifier, vcs: Seq[VerificationCondition], specgen: Boolean): Program = {

    var defs: Seq[Definition] = Seq.empty

    for (vc <- vcs) {
      val f = vc.funDef
      val id = f.id
      val returnType = getNonRealType(f.returnType)
      val args: Seq[VarDecl] = f.args.map(decl => VarDecl(decl.id, getNonRealType(decl.tpe)))

      val body = f.body
      val funDef = new FunDef(id, returnType, args)
      funDef.body = body

      f.precondition match {
        case Some(p) => funDef.precondition = Some(specTransformer.transform(f.precondition.get))
        case None => ;
      }

      if (specgen) {
        funDef.postcondition = vc.generatedPost
      } else {
        funDef.postcondition = f.postcondition
      }
      defs = defs :+ funDef
    }
    val invariants: Seq[Expr] = Seq.empty

    val newProgram = Program(programId, ObjectDef(objectId, defs, invariants))
    newProgram

  }

  def getNonRealType(tpe: TypeTree): TypeTree = (tpe, precision) match {
    case (RealType, Float64) => Float64Type
    case (RealType, Float32) => Float32Type
    case (RealType, DoubleDouble) => FloatDDType
    case (RealType, QuadDouble) => FloatQDType
    case _ => tpe
  }

  /*
    Replaces all constructs related to Real's with something meant to compile.
  */
  class SpecTransformer extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case Roundoff(expr) => BooleanLiteral(true)
      case _ =>
        super.rec(e, path)
    }

  }*/

}
