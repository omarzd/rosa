package leon
package numerics

import purescala.Trees._
import affine.XFloat

case class Path(condition: Expr, expression: List[Expr]) {
  var value: Option[XFloat] = None

  def addCondition(c: Expr): Path =
    Path(And(condition, c), expression)

  def addPath(p: Path): Path = {
    Path(And(this.condition, p.condition), this.expression ++ p.expression)
  }

  def addEqualsToLast(e: Expr): Path = {
    Path(condition, expression.init ++ List(Equals(e, expression.last)))
  }
}

