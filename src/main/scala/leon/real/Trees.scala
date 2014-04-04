/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import purescala.Common._
import purescala.TypeTrees._
import purescala.TypeTreeOps.leastUpperBound
import purescala.Trees._
import purescala.Definitions._
import purescala.Extractors._
import purescala.{PrettyPrinter, PrettyPrintable, ScalaPrinter}

object Trees {

  case class RealLiteral(value: Rational) extends Expr with Terminal with FixedType with PrettyPrintable {
    var floatType = false // for code generation of single-precision floating-point constants
    val fixedType = RealType
    def this(d: Double) = this(Rational(d))
    def this(i: Int) = this(Rational(i))

    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      if (floatType) printer.append(value.toString + "f")
      else printer.append(value.toString)
    }
  }

  // literal in the floating-point computation
  case class FloatLiteral(value: Rational, exact: Boolean) extends Expr with Terminal with FixedType with PrettyPrintable {
    val fixedType = RealType

    def this(r: Rational) = this(r, isExact(r))
    def this(d: Double) = this(Rational(d))
    def this(i: Int) = this(Rational(i), true)

    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append(value.toString + "f")
    }
  }

  case class LongLiteral(value: Long) extends Expr with Terminal with FixedType with PrettyPrintable {
    val fixedType = Int64Type
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append(value.toString + "l")
    }
  }

  /* Adds an uncertainty of absolute magnitude error to the expression varr. */
  case class Noise(varr: Expr, error: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable {
    val fixedType = BooleanType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((varr, error, (t1, t2) => Noise(t1, t2)))
    }

    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("noise(")
      printer.pp(varr, Some(this))
      printer.append(", ")
      printer.pp(error, Some(this))
      printer.append(")")
    }
  }

  // Marks that a variable should have initial roundoff in translation to Z3.
  case class Roundoff(expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = BooleanType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => Roundoff(e)))
    }
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("rndoof(")
      printer.pp(expr, Some(this))
      printer.append(")")
    }
  }

  /* Reference to the actually computed floating-point (or other) value (as opposed to the ideal real one). */
  case class Actual(expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => Actual(e)))
    }
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("~")
      printer.pp(expr, Some(this))
    }
  }

  /* Bounds of the expression varr. */
  case class WithIn(varr: Expr, lwrBnd: Rational, upBnd: Rational) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = BooleanType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((varr, (e) => WithIn(e, lwrBnd, upBnd)))
    }
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.pp(varr, Some(this))
      printer.append(" \u2208 [")
      printer.append(lwrBnd.toString)
      printer.append(",")
      printer.append(upBnd.toString)
      printer.append("]")
    }
  }


  case class InitialNoise(expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = RealType

    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => InitialNoise(e)))
    }
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("!")
      printer.pp(expr, Some(this))
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

    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("relError(")
      printer.pp(expr, Some(this))
      printer.append(", ")
      printer.pp(err, Some(this))
      printer.append(")")
    }
  }

  case class Assertion(expr: Expr) extends Expr with FixedType  with UnaryExtractable with PrettyPrintable {
    val fixedType = BooleanType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => Assertion(e)))
    }
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("assert(")
      printer.pp(expr, Some(this))
      printer.append(")")
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

    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("(")
      printer.pp(lhs, Some(this))
      printer.append(" + ")
      printer.pp(rhs, Some(this))
      printer.append(")")
    }
  }
  case class MinusR(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable with RealArithmetic {
    val fixedType = RealType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => MinusR(t1, t2)))
    }
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("(")
      printer.pp(lhs, Some(this))
      printer.append(" - ")
      printer.pp(rhs, Some(this))
      printer.append(")")
    }
  }
  case class UMinusR(expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable with RealArithmetic {
    val fixedType = RealType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => UMinusR(e)))
    }
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("(-")
      printer.pp(expr, Some(this))
      printer.append(")")
    }
  }
  case class TimesR(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable with RealArithmetic {
    val fixedType = RealType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => TimesR(t1, t2)))
    }
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("(")
      printer.pp(lhs, Some(this))
      printer.append(" * ")
      printer.pp(rhs, Some(this))
      printer.append(")")
    }
  }
  case class DivisionR(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable with RealArithmetic {
    val fixedType = RealType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => DivisionR(t1, t2)))
    }
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("(")
      printer.pp(lhs, Some(this))
      printer.append(" / ")
      printer.pp(rhs, Some(this))
      printer.append(")")
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
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("(")
      printer.pp(lhs, Some(this))
      printer.append(" ^ ")
      printer.pp(rhs, Some(this))
      printer.append(")")
    }
  }
  case class SqrtR(expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable with RealArithmetic {
    val fixedType = RealType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => SqrtR(e)))
    }
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("sqrt(")
      printer.pp(expr, Some(this))
      printer.append(")")
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
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("(")
      (exprs.init).foreach(e => {
        printer.pp(e, Some(this))
        printer.append(" * ")
      })
      printer.pp(exprs.last, Some(this))
      printer.append(")")
    }
  }



  /* Arithmetic on floats */
  case class PlusF(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => PlusF(t1, t2)))
    }

    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("(")
      printer.pp(lhs, Some(this))
      printer.append(" \u2295 ")
      printer.pp(rhs, Some(this))
      printer.append(")")
    }
  }
  case class MinusF(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => MinusF(t1, t2)))
    }
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("(")
      printer.pp(lhs, Some(this))
      printer.append(" \u2296 ")
      printer.pp(rhs, Some(this))
      printer.append(")")
    }
  }
  case class UMinusF(expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => UMinusF(e)))
    }
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("(\u2296")
      printer.pp(expr, Some(this))
      printer.append(")")
    }
  }
  case class TimesF(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => TimesF(t1, t2)))
    }
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("(")
      printer.pp(lhs, Some(this))
      printer.append(" \u2297 ")
      printer.pp(rhs, Some(this))
      printer.append(")")
    }
  }
  case class DivisionF(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => DivisionF(t1, t2)))
    }
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("(")
      printer.pp(lhs, Some(this))
      printer.append(" \u2298 ")
      printer.pp(rhs, Some(this))
      printer.append(")")
    }
  }
  case class SqrtF(expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => SqrtF(e)))
    }
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("sqrtF(")
      printer.pp(expr, Some(this))
      printer.append(")")
    }
  }

  // A value returned from a function call described by it's specification
  //@param model whether this function call came from a @model
  case class FncValue(spec: Seq[Spec], specExpr: Expr, model: Boolean) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((specExpr, (e) => FncValue(spec, e, model)))
    }
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("fncVal(" + spec.toString + "-")
      printer.pp(specExpr, Some(this))
      printer.append(model + ")")
    }
  }

  case class FncValueF(spec: Seq[Spec], specExpr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((specExpr, (e) => FncValueF(spec, e)))
    }
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("fncValF(" + spec.toString + ")(")
      printer.pp(specExpr, Some(this))
      printer.append(")")
    }
  }

  // A value returned from a function call desribed by it's specification
  case class FncBody(name: String, body: Expr, funDef: FunDef, params: Seq[Expr]) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((body, (e) => FncBody(name, e, funDef, params)))
    }
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("fnc_" + name + "(")
      printer.pp(body, Some(this))
      printer.append(")")
    }
  }

  case class FncBodyF(name: String, body: Expr, funDef: FunDef, params: Seq[Expr]) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((body, (e) => FncBodyF(name, e, funDef, params)))
    }
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("fnc_" + name + "_f(")
      printer.pp(body, Some(this))
      printer.append(")")
    }
  }


  // approximates some other expression
  case class ApproxNode(xfloat: XReal) extends Expr with FixedType with Terminal with PrettyPrintable {
    val fixedType = RealType
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("approx(")
      printer.append(xfloat.toString)
      printer.append(")")
    }
  }

  case class FloatIfExpr(cond: Expr, thenn: Expr, elze: Expr) extends Expr with FixedType with NAryExtractable with PrettyPrintable {
    val fixedType = leastUpperBound(thenn.getType, elze.getType).getOrElse(AnyType)

    def extract: Option[(Seq[Expr], (Seq[Expr])=>Expr)] = {
      Some((Seq(cond, thenn, elze), (es) => FloatIfExpr(es(0), es(1), es(2))))
    }

    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("iff (")
      printer.pp(cond, Some(this))
      printer.append(")\n")
      printer.ind(lvl + 1)
      printer.pp(thenn, Some(this))(lvl + 1)
      printer.append("\n")
      printer.ind(lvl)
      printer.append("elsse\n")
      printer.ind(lvl + 1)
      printer.pp(elze, Some(this))(lvl + 1)
    }
  }

  case class FncInvocationF(funDef: TypedFunDef, args: Seq[Expr]) extends Expr with FixedType with NAryExtractable with PrettyPrintable {
    //assert(funDef.returnType == RealType)  doesn't hold any more with tuples
    val fixedType = RealType

    def extract: Option[(Seq[Expr], (Seq[Expr])=>Expr)] = {
      Some((args, (es) => FncInvocationF(funDef, es)))
    }

    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append(funDef.id.name + "_f(")
      (args.init).foreach(e => {
        printer.pp(e,  Some(this))
        printer.append(", ")
      })
      printer.pp(args.last, Some(this))
      printer.append(")")
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
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("(")
      printer.pp(left, Some(this))
      printer.append(" === ")
      printer.pp(right, Some(this))
      printer.append(")")
    }
  }

  case class RightShift(expr: Expr, bits: Int) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = Int32Type
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => RightShift(e, bits)))
    }
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("(")
      printer.pp(expr, Some(this))
      printer.append(" >> ")
      printer.append(bits.toString)
      printer.append(")")
    }
  }

  case class LeftShift(expr: Expr, bits: Int) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = Int32Type
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => LeftShift(e, bits)))
    }
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("(")
      printer.pp(expr, Some(this))
      printer.append(" << ")
      printer.append(bits.toString)
      printer.append(")")
    }
  }

  case class ValAssignment(varId: Identifier, expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = UnitType

    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, ValAssignment(varId, _)))
    }

    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("val ")
      printer.append(varId.name)
      printer.append(" = ")
      printer.pp(expr, Some(this))
      printer.append("")
    }
  }

  case class UpdateFunction(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable {
    val fixedType = UnitType

    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => UpdateFunction(t1, t2)))
    }
    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("(")
      printer.pp(lhs, Some(this))
      printer.append(" <== ")
      printer.pp(rhs, Some(this))
      printer.append(")")
    }
  } 

  case class Iteration(ids: Seq[Identifier], body: Expr, updateFncs: Seq[Expr]) extends Expr with FixedType with NAryExtractable with PrettyPrintable {
    val fixedType = TupleType(ids.map(i => RealType))

    def extract: Option[(Seq[Expr], (Seq[Expr])=>Expr)] = {
      Some((Seq(body) ++ updateFncs, (es) => Iteration(ids, es(0), es.tail)))
    }

    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("iterate (")
      printer.append(ids.mkString(", "))
      printer.append(") {\n")
      printer.pp(body, Some(this))(lvl + 1)
      printer.append("\n")
      (updateFncs.init).foreach(e => {
        printer.pp(e,  Some(this))(lvl + 1)
        printer.append("\n")
      })
      printer.pp(updateFncs.last, Some(this))
      printer.append("}")
    }
  }

  case class LoopCounter(id: Identifier) extends Expr with Terminal with FixedType with PrettyPrintable {
    val fixedType = BooleanType

    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("loopCounter(" + id + ")")
    }
  }

  case class IntegerValue(id: Identifier) extends Expr with Terminal with FixedType with PrettyPrintable {
    val fixedType = BooleanType

    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("integer(" + id + ")")
    }
  } 
}
