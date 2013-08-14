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

  case class RationalLiteral(value: Rational) extends Expr with Terminal with FixedType with PrettyPrintable {
    def this(d: Double) = this(Rational(d))
    def this(i: Int) = this(Rational(i))
    val fixedType = RealType

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

}