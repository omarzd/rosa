/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Common._
import purescala.TypeTrees._
import purescala.TypeTreeOps.leastUpperBound
import purescala.Trees._
import purescala.Definitions._
import purescala.Extractors._
import purescala.{PrettyPrinter, PrettyPrintable, ScalaPrinter, PrinterContext}

object Trees {
  import purescala.PrinterHelpers._

  case class RealLiteral(value: Rational) extends Expr with Terminal with FixedType with PrettyPrintable {
    var floatType = false // for code generation of single-precision floating-point constants
    val fixedType = RealType
    def this(d: Double) = this(Rational.rationalFromReal(d))
    def this(i: Int) = this(Rational(i))

    def printWith(implicit pctx: PrinterContext) {
      if (floatType) p"${value.toString}f"
      else p"${value.toString}"
    }
  }

  // literal in the floating-point computation
  case class FloatLiteral(value: Rational) extends Expr with Terminal with FixedType with PrettyPrintable {
    val fixedType = RealType

    def this(d: Double) = this(Rational.rationalFromReal(d))
    def this(i: Int) = this(Rational(i))

    def printWith(implicit pctx: PrinterContext) {
      p"${value.toString}f"
    }
  }

  case class LongLiteral(value: Long) extends Expr with Terminal with FixedType with PrettyPrintable {
    val fixedType = Int64Type
    def printWith(implicit pctx: PrinterContext) {
      p"${value.toString}l"
    }
  }

  /* Adds an uncertainty of absolute magnitude error to the expression varr. */
  case class Noise(varr: Expr, error: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable {
    val fixedType = BooleanType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((varr, error, (t1, t2) => Noise(t1, t2)))
    }

    def printWith(implicit pctx: PrinterContext) {
      p"($varr +/- $error)"
    }
  }

  // Marks that a variable should have initial roundoff in translation to Z3.
  case class Roundoff(expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = BooleanType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => Roundoff(e)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"rndoof($expr)"
    }
  }

  /* Reference to the actually computed floating-point (or other) value (as opposed to the ideal real one). */
  case class Actual(expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => Actual(e)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"~$expr"
    }
  }

  /* Bounds of the expression varr. */
  case class WithIn(varr: Expr, lwrBnd: Rational, upBnd: Rational) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    assert(lwrBnd <= upBnd)
    val fixedType = BooleanType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((varr, (e) => WithIn(e, lwrBnd, upBnd)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"$varr \u2208 ($lwrBnd, $upBnd)"
    }
  }

  case class WithInEq(varr: Expr, lwrBnd: Rational, upBnd: Rational) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    assert(lwrBnd <= upBnd)
    val fixedType = BooleanType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((varr, (e) => WithInEq(e, lwrBnd, upBnd)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"$varr \u2208 [$lwrBnd, $upBnd]"
    }
  }


  case class InitialNoise(expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = RealType

    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => InitialNoise(e)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"!$expr"
    }
  }

  case class RelError(expr: Expr, err: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable {
    val fixedType = BooleanType

    err match {
      case RealLiteral(value) => assert(value > Rational.zero)
    }

    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((expr, err, (t1, t2) => RelError(t1, t2)))
    }

    def printWith(implicit pctx: PrinterContext) {
      p"relError($expr, $err)"
    }
  }

  case class Assertion(expr: Expr) extends Expr with FixedType  with UnaryExtractable with PrettyPrintable {
    val fixedType = BooleanType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => Assertion(e)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"assert($expr)"
    }
  }

  trait RealArithmetic {
    self: Expr =>
  }

  /* Arithmetic on reals */
  case class PlusR(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable with RealArithmetic {
    val fixedType = RealType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => PlusR(t1, t2)))
    }

    def printWith(implicit pctx: PrinterContext) {
      p"($lhs + $rhs)"
    }
  }
  case class MinusR(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable with RealArithmetic {
    val fixedType = RealType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => MinusR(t1, t2)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"($lhs - $rhs)"
    }
  }
  case class UMinusR(expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable with RealArithmetic {
    val fixedType = RealType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => UMinusR(e)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"(-$expr)"
    }
  }
  case class TimesR(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable with RealArithmetic {
    val fixedType = RealType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => TimesR(t1, t2)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"($lhs * $rhs)"
    }
  }
  case class DivisionR(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable with RealArithmetic {
    val fixedType = RealType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => DivisionR(t1, t2)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"($lhs / $rhs)"
    }
  }
  case class PowerR(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable with RealArithmetic {
    val fixedType = RealType
    /*rhs match {
      case IntLiteral(i) => assert (i > 1)
    }*/
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => PowerR(t1, t2)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"($lhs ^ $rhs)"
    }
  }
  case class SqrtR(expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable with RealArithmetic {
    val fixedType = RealType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => SqrtR(e)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"sqrt($expr)"
    }
  }

  // Only use Product for ideal/real values, as for actual values the order of computation matters.
  object Product {
    def apply(l: Expr, r: Expr) : Expr = Product(Seq(l, r))
    def apply(exprs: Seq[Expr]) : Expr = {
      val flat = exprs.flatMap(_ match {
        case Product(es) => es
        case o => Seq(o)
      })
      new Product(flat)
    }
    def unapply(prod: Product) : Option[Seq[Expr]] =
      if(prod == null) None else Some(prod.exprs)
  }
  class Product private (val exprs: Seq[Expr]) extends Expr with FixedType with NAryExtractable with PrettyPrintable{
    val fixedType = RealType
    assert(exprs.size >= 2)
    override def equals(that: Any): Boolean = (that != null) && (that match {
      case t: Product => t.exprs == exprs
      case _ => false
    })

    override def hashCode: Int = exprs.hashCode

    def extract: Option[(Seq[Expr], (Seq[Expr])=>Expr)] = {
      Some((exprs, (es) => Product(es)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"""(${exprs.mkString(" * ")})"""
    }
  }



  /* Arithmetic on floats */
  case class PlusF(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => PlusF(t1, t2)))
    }

    def printWith(implicit pctx: PrinterContext) {
      p"($lhs \u2295 $rhs)"
    }
  }
  case class MinusF(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => MinusF(t1, t2)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"($lhs \u2296 $rhs)"
    }
  }
  case class UMinusF(expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => UMinusF(e)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"(\u2296 $expr)"
    }
  }
  case class TimesF(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => TimesF(t1, t2)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"($lhs \u2297 $rhs)"
    }
  }
  case class DivisionF(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => DivisionF(t1, t2)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"($lhs \u2298 $rhs)"
    }
  }
  case class SqrtF(expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => SqrtF(e)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"sqrtF($expr)"
    }
  }

  // A value returned from a function call described by it's specification
  //@param model whether this function call came from a @model
  case class FncValue(spec: Seq[Spec], specExpr: Expr, model: Boolean, funDef: FunDef, params: Seq[Expr]) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = RealType

    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((specExpr, (e) => FncValue(spec, e, model, funDef, params)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"fncVal(${spec.toString}-$specExpr-$model)"
    }
  }

  case class FncValueF(spec: Seq[Spec], specExpr: Expr, funDef: FunDef, params: Seq[Expr]) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((specExpr, (e) => FncValueF(spec, e, funDef, params)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"fncValF(${spec.toString})($specExpr)"
    }
  }

  // A value returned from a function call desribed by it's specification
  case class FncBody(name: String, body: Expr, funDef: FunDef, params: Seq[Expr]) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((body, (e) => FncBody(name, e, funDef, params)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"fnc_$name($body)"
    }
  }

  case class FncBodyF(name: String, body: Expr, funDef: FunDef, params: Seq[Expr]) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((body, (e) => FncBodyF(name, e, funDef, params)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"fnc_${name}_f($body)"
    }
  }


  // approximates some other expression
  case class ApproxNode(xfloat: XReal) extends Expr with FixedType with Terminal with PrettyPrintable {
    val fixedType = RealType
    def printWith(implicit pctx: PrinterContext) {
      p"approx($xfloat)"
    }
  }

  case class FloatIfExpr(cond: Expr, thenn: Expr, elze: Expr) extends Expr with FixedType with NAryExtractable with PrettyPrintable {
    val fixedType = leastUpperBound(thenn.getType, elze.getType).getOrElse(Untyped)

    def extract: Option[(Seq[Expr], (Seq[Expr])=>Expr)] = {
      Some((Seq(cond, thenn, elze), (es) => FloatIfExpr(es(0), es(1), es(2))))
    }

    def printWith(implicit pctx: PrinterContext) {
      p"""|iff ($cond){
          |  $thenn
          |} elsse
          |  $elze
          |}
          """
    }
  }

  case class FncInvocationF(funDef: TypedFunDef, args: Seq[Expr]) extends Expr with FixedType with NAryExtractable with PrettyPrintable {
    //assert(funDef.returnType == RealType)  doesn't hold any more with tuples
    val fixedType = RealType

    def extract: Option[(Seq[Expr], (Seq[Expr])=>Expr)] = {
      Some((args, (es) => FncInvocationF(funDef, es)))
    }

    def printWith(implicit pctx: PrinterContext) {
      p"""${funDef.id.name}_f(${args.mkString(", ")})"""
    }
  }

  case class EqualsF(left: Expr, right: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable {
    val fixedType = BooleanType

    override def equals(that: Any): Boolean = (that != null) && (that match {
      case t: EqualsF => t.left == left && t.right == right
      case _ => false
    })

    override def hashCode: Int = left.hashCode+right.hashCode

    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((left, right, (t1, t2) => EqualsF(t1, t2)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"($left === $right)"
    }
  }

  case class RightShift(expr: Expr, bits: Int) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = Int32Type
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => RightShift(e, bits)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"($expr >> $bits)"
    }
  }

  case class LeftShift(expr: Expr, bits: Int) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = Int32Type
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => LeftShift(e, bits)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"($expr << $bits)"
    }
  }

  case class ValAssignment(varId: Identifier, expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = UnitType

    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, ValAssignment(varId, _)))
    }

    def printWith(implicit pctx: PrinterContext) {
      p"val ${varId.name} = $expr"
    }
  }

  case class UpdateFunction(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable {
    val fixedType = UnitType

    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => UpdateFunction(t1, t2)))
    }
    def printWith(implicit pctx: PrinterContext) {
      p"($lhs <== $rhs)"
    }
  }

  case class InitialErrors(expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = BooleanType

    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, InitialErrors(_)))
    }

    def printWith(implicit pctx: PrinterContext) {
      p"initialErrors($expr)"
    }
  }


  case class DocComment(args: Seq[Expr]) extends Expr with NAryExtractable {
    def extract: Option[(Seq[Expr], (Seq[Expr])=>Expr)] = {
      Some((args, DocComment(_)))
    }

    /*def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("/*")
      (args.init).foreach(e => {
        printer.pp(e,  Some(this))
        printer.append("\n")
      })
      printer.pp(args.last, Some(this))
      printer.append("*/")
    }*/
  }

  case class DocLine(tag: String, expr: Expr) extends Expr with UnaryExtractable with PrettyPrintable {
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, DocLine(tag, _)))
    }

    def printWith(implicit pctx: PrinterContext) {
      p"@$tag $expr"
    }
  }

  case class Iteration(ids: Seq[Identifier], body: Expr, updateFncs: Seq[Expr]) extends Expr with FixedType with NAryExtractable with PrettyPrintable {
    val fixedType = TupleType(ids.map(i => RealType))

    def extract: Option[(Seq[Expr], (Seq[Expr])=>Expr)] = {
      Some((Seq(body) ++ updateFncs, (es) => Iteration(ids, es(0), es.tail)))
    }

    def printWith(implicit pctx: PrinterContext) {
      p"""iterate (${ids.mkString(", ")})\n ${body} \n ${updateFncs.mkString("\n")} }"""
    }
  }

}
