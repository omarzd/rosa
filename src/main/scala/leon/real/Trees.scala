/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import leon.purescala.Common._
import leon.purescala.TypeTrees._
import leon.purescala.Trees._
import leon.purescala.Definitions._
import leon.purescala.Extractors._
import leon.purescala.{PrettyPrinter, PrettyPrintable, ScalaPrinter}

object Trees {


  // represents the actual result in post-conditions
  case class FResVariable() extends Expr with Terminal with FixedType with PrettyPrintable {
    val fixedType = FloatType
    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("#fres")
    }
  }

  case class RationalLiteral(value: Rational) extends Expr with Terminal with FixedType with PrettyPrintable {
    var exact = isExact(value)

    def this(r: Rational, e: Boolean) = {
      this(r)
      exact = e
    }
    def this(d: Double) = this(Rational(d))
    def this(i: Int) = this(Rational(i))
    val fixedType = RealType // TODO: this should not be fixedType (mark as float those that should have rndoff error)

    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append(value.toString)
    }
  }

  /* Adds an uncertainty of absolute magnitude error to the expression varr. */
  case class Noise(varr: Expr, error: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable {
    val fixedType = BooleanType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((varr, error, (t1, t2) => Noise(t1, t2)))
    }

    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("noise(")
      printer.pp(varr,lvl)
      printer.append(", ")
      printer.pp(error,lvl)
      printer.append(")")
    }
  }

  // Marks that a variable should have initial roundoff in translation to Z3.
  case class Roundoff(expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = BooleanType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => Actual(e)))
    }
    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("rndoof(")
      printer.pp(expr,lvl)
      printer.append(")")
    }
  }

  /* Reference to the actually computed floating-point (or other) value (as opposed to the ideal real one). */
  case class Actual(expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => Actual(e)))
    }
    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("~")
      printer.pp(expr,lvl)
    }
  }

  /* Bounds of the expression varr. */
  case class WithIn(varr: Expr, lwrBnd: Rational, upBnd: Rational) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = BooleanType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((varr, (e) => WithIn(e, lwrBnd, upBnd)))
    }
    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.pp(varr,lvl)
      printer.append(" \u2208 [")
      printer.append(lwrBnd.toString)
      printer.append(",")
      printer.append(upBnd.toString)
      printer.append("]")
    }
  }

  /*
  case class InitialNoise(expr: Expr) extends Expr with FixedType {
    val fixedType = RealType
  }*/
  /*
  case class RelError(expr: Expr, err: Expr) extends Expr with FixedType {
    val fixedType = BooleanType
  } */ 

  case class Assertion(expr: Expr) extends Expr with FixedType  with UnaryExtractable with PrettyPrintable {
    val fixedType = BooleanType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => Assertion(e)))
    }
    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("assert(")
      printer.pp(expr,lvl)
      printer.append(")")
    }
  }

  /* Arithmetic on reals */
  case class PlusR(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => PlusR(t1, t2)))
    }

    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("(")
      printer.pp(lhs,lvl)
      printer.append(" + ")
      printer.pp(rhs,lvl)
      printer.append(")")
    }
  }
  case class MinusR(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => MinusR(t1, t2)))
    }
    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("(")
      printer.pp(lhs,lvl)
      printer.append(" - ")
      printer.pp(rhs,lvl)
      printer.append(")")
    }
  }
  case class UMinusR(expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => UMinusR(e)))
    }
    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("(-")
      printer.pp(expr,lvl)
      printer.append(")")
    }
  }
  case class TimesR(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => TimesR(t1, t2)))
    }
    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("(")
      printer.pp(lhs,lvl)
      printer.append(" * ")
      printer.pp(rhs,lvl)
      printer.append(")")
    }
  }
  case class DivisionR(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => DivisionR(t1, t2)))
    }
    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("(")
      printer.pp(lhs,lvl)
      printer.append(" / ")
      printer.pp(rhs,lvl)
      printer.append(")")
    }
  }
  case class PowerR(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => PowerR(t1, t2)))
    }
    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("(")
      printer.pp(lhs,lvl)
      printer.append(" ^ ")
      printer.pp(rhs,lvl)
      printer.append(")")
    }
  }
  case class SqrtR(expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => SqrtR(e)))
    }
    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("sqrt(")
      printer.pp(expr,lvl)
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
    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("(")
      (exprs.init).foreach(e => {
        printer.pp(e, lvl)
        printer.append(" * ")
      })
      printer.pp(exprs.last,lvl)
      printer.append(")")
    }
  }

  

  /* Arithmetic on floats */
  case class PlusF(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable {
    val fixedType = FloatType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => PlusF(t1, t2)))
    }

    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("(")
      printer.pp(lhs,lvl)
      printer.append(" \u2295 ")
      printer.pp(rhs,lvl)
      printer.append(")")
    }
  }
  case class MinusF(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable {
    val fixedType = FloatType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => MinusF(t1, t2)))
    }
    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("(")
      printer.pp(lhs,lvl)
      printer.append(" \u2296 ")
      printer.pp(rhs,lvl)
      printer.append(")")
    }
  }
  case class UMinusF(expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = FloatType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => UMinusF(e)))
    }
    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("(\u2296")
      printer.pp(expr,lvl)
      printer.append(")")
    }
  }
  case class TimesF(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable {
    val fixedType = FloatType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => TimesF(t1, t2)))
    }
    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("(")
      printer.pp(lhs,lvl)
      printer.append(" \u2297 ")
      printer.pp(rhs,lvl)
      printer.append(")")
    }
  }
  case class DivisionF(lhs: Expr, rhs: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable {
    val fixedType = FloatType
    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((lhs, rhs, (t1, t2) => DivisionF(t1, t2)))
    }
    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("(")
      printer.pp(lhs,lvl)
      printer.append(" \u2298 ")
      printer.pp(rhs,lvl)
      printer.append(")")
    }
  }
  case class SqrtF(expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = FloatType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e) => SqrtF(e)))
    }
    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("sqrtF(")
      printer.pp(expr,lvl)
      printer.append(")")
    }
  }

  // A value returned from a function call desribed by it's specification
  case class FncValue(spec: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((spec, (e) => FncValue(e)))
    }
    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("fncVal(")
      printer.pp(spec,lvl)
      printer.append(")")
    }
  }

  case class FncValueF(spec: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = FloatType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((spec, (e) => FncValueF(e)))
    }
    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("fncVal_f(")
      printer.pp(spec,lvl)
      printer.append(")")
    }
  }

  // A value returned from a function call desribed by it's specification
  case class FncBody(name: String, body: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = RealType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((body, (e) => FncBody(name, e)))
    }
    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("fnc_"+name+"(")
      printer.pp(body,lvl)
      printer.append(")")
    }
  }

  case class FncBodyF(name: String, body: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = FloatType
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((body, (e) => FncBodyF(name, e)))
    }
    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("fnc_"+name+"_f(")
      printer.pp(body,lvl)
      printer.append(")")
    }
  }


  // approximates some other expression
  case class ApproxNode(xfloat: XFloat) extends Expr with FixedType with Terminal with PrettyPrintable {
    val fixedType = FloatType
    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("approx(")
      printer.append(xfloat.toString)
      printer.append(")")
    }
  }

}