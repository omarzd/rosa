/* Copyright 2013 EPFL, Lausanne */

package leon
package real

import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.TypeTrees._

import leon.real.Trees._


object SMTLib {

  def printSMTLib2(e: Expr): Seq[String] = {
    var lines = Seq[String]()
    lines :+= "(set-logic QF_NRA)"

    // declare all variables
    val allIDs = variablesOf(e)
    allIDs.foreach {
      case id if (id.getType == RealType) =>
        val name = id.uniqueName.replace('#', '_')
        lines :+= "(declare-fun %s () Real)".format(name)
    }

    e match {
      case And(args) =>
        args.foreach { a =>
          lines :+= "(assert %s )".format(toPrefix(a))}

      case _ =>
        lines :+= "Expr did not match And(_)"
    }

    lines
  }

  def toPrefix(e: Expr): String = e match {
    case LessThan(l, r) => "(< %s %s)".format(toPrefix(l), toPrefix(r))
    case LessEquals(l, r) => "(<= %s %s)".format(toPrefix(l), toPrefix(r))
    case GreaterThan(l, r) => "(> %s %s)".format(toPrefix(l), toPrefix(r))
    case GreaterEquals(l, r) => "(>= %s %s)".format(toPrefix(l), toPrefix(r))

    case Equals(l, r) => "(= %s %s)".format(toPrefix(l), toPrefix(r))

    case PlusR(l, r) => "(+ %s %s)".format(toPrefix(l), toPrefix(r))
    case MinusR(l, r) => "(- %s %s)".format(toPrefix(l), toPrefix(r))
    case TimesR(l, r) => "(* %s %s)".format(toPrefix(l), toPrefix(r))
    case DivisionR(l, r) => "(/ %s %s)".format(toPrefix(l), toPrefix(r))
    case UMinusR(l) => "(- %s)".format(toPrefix(l))
    // TODO: this should be made a proper real
    case RealLiteral(r) =>
      val decimal = "%.40f".format(r.toDouble)
      decimal.replaceAll("0*$", "")
    case Variable(id) => id.uniqueName.replace('#', '_')
    case PowerR(l, r) => "(^ %s %s)".format(toPrefix(l), toPrefix(r))
    case IntLiteral(i) => i.toString

    case Or(args) =>
      "(or %s)".format(args.map(a => toPrefix(a)).mkString(" "))

    case Not(l) =>
      "(not %s)".format(toPrefix(l))

    case And(args) =>
      "(and %s)".format(args.map(a => toPrefix(a)).mkString(" "))

  }

}
