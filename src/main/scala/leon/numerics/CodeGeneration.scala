package leon
package numerics

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import Precision._

class CodeGeneration(reporter: Reporter, precision: Precision) {
  val specTransformer = new SpecTransformer

  // Produces something that does not typecheck. But printed it should be fine.
  def specToCode(program: Program, vcs: Seq[VerificationCondition]): Program = {

    val objDef = program.mainObject

    var defs: Seq[Definition] = Seq.empty

    for (deff <- objDef.defs) {
      deff match {
        case f: FunDef =>
          val id = f.id
          val returnType = getNonRealType(f.returnType)
          val args: Seq[VarDecl] = f.args.map(decl => 
            VarDecl(decl.id, getNonRealType(decl.tpe))
          )

          val body = f.body
          val pre = specTransformer.transform(f.precondition.get)
          val post = specTransformer.transform(f.postcondition.get)
          val funDef = new FunDef(id, returnType, args)
          funDef.body = body
          funDef.precondition = Some(pre)
          funDef.postcondition = Some(post)
          defs = defs :+ funDef
          
        case _ =>
          reporter.warning("Cannot handle this definition: " + deff.getClass)
      }

    }
    val invariants: Seq[Expr] = Seq.empty

    val newProgram = Program(program.id, ObjectDef(objDef.id, defs, invariants))
    newProgram

  }

  // TODO: this should be parametric in which float we tested
  def getNonRealType(tpe: TypeTree): TypeTree = (tpe, precision) match {
    case (RealType, Float64) => Float64Type
    case (RealType, Float32) => Float32Type
    case _ => tpe
  }

  /*
    Replaces all constructs related to Real's with something meant to compile.
  */
  class SpecTransformer extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil

    // TODO: do we need this?
    def register(e: Expr, path: C) = path :+ e

    override def rec(e: Expr, path: C) = e match {
      case Noise(_, _) => BooleanLiteral(true)
      case Roundoff(expr) => BooleanLiteral(true)
      case _ =>
        super.rec(e, path)
    }

  }

}
