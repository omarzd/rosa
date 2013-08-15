/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._

import real.Trees._


object ArithmeticOps {

  def idealToActual(expr: Expr, vars: VariableStore): Expr = {
    val transformer = new RealToFloatTransformer(vars)
    transformer.transform(expr) 
  }

  private class RealToFloatTransformer(variables: VariableStore) extends TransformerWithPC {
    type C = Seq[Expr]
    val initC = Nil
    
    def register(e: Expr, path: C) = path :+ e

    // (Sound) Overapproximation in the case of strict inequalities
    override def rec(e: Expr, path: C) = e match {
      case UMinusR(t) => UMinusF(rec(t, path))
      case PlusR(lhs, rhs) => PlusF(rec(lhs, path), rec(rhs, path))
      case MinusR(lhs, rhs) => MinusF(rec(lhs, path), rec(rhs, path))
      case TimesR(lhs, rhs) => TimesF(rec(lhs, path), rec(rhs, path))
      case DivisionR(lhs, rhs) => DivisionF(rec(lhs, path), rec(rhs, path))
      case SqrtR(t) => SqrtF(rec(t, path))
      case v: Variable => variables.buddy(v)
      case ResultVariable() => FResVariable()

      case _ =>
        super.rec(e, path)
    }
  }

}