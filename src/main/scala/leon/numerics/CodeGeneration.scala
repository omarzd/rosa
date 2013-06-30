package leon
package numerics

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import Precision._
import SpecGenType._

class CodeGeneration(reporter: Reporter, precision: Precision) {
  val specTransformer = new SpecTransformer


  val noiseDefSingle = new FunDef(FreshIdentifier("noise"), BooleanType, Seq(VarDecl(FreshIdentifier("x"), Float32Type)))
  noiseDefSingle.body = Some(BooleanLiteral(true))

  val noiseDefDouble = new FunDef(FreshIdentifier("noise"), BooleanType, Seq(VarDecl(FreshIdentifier("x"), Float64Type)))
  noiseDefDouble.body = Some(BooleanLiteral(true))

  val noiseDefDDouble = new FunDef(FreshIdentifier("noise"), BooleanType, Seq(VarDecl(FreshIdentifier("x"), FloatDDType)))
  noiseDefDDouble.body = Some(BooleanLiteral(true))

  val noiseDefQDouble = new FunDef(FreshIdentifier("noise"), BooleanType, Seq(VarDecl(FreshIdentifier("x"), FloatQDType)))
  noiseDefQDouble.body = Some(BooleanLiteral(true))


  def specToCode(programId: Identifier, objectId: Identifier, vcs: Seq[VerificationCondition], specGenType: SpecGenType): Program = {

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

      if (specGenType != None) {
        funDef.postcondition = vc.generatedPost
      } else {
        funDef.postcondition = f.postcondition
      }
      defs = defs :+ funDef
    }
    val invariants: Seq[Expr] = Seq.empty

    precision match {
      case Float32 => defs = defs :+ noiseDefSingle
      case Float64 => defs = defs :+ noiseDefDouble
      case DoubleDouble => defs = defs :+ noiseDefDDouble
      case QuadDouble => defs = defs :+ noiseDefQDouble
    }

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

  }

}
