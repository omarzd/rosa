/* Copyright 2013-2014 EPFL, Lausanne */

package leon
package real

import purescala.Trees.{Expr}

object EMatrix {
  // sequence of rows
  def fromSeqs(es: Seq[Seq[Expr]]): EMatrix = {
    new EMatrix(es(0).length, es)
  }

}

// square matrix
trait Matrix[T] {
  val data: Seq[Seq[T]]
  def apply(i: Int, j: Int) = data(i)(j)

  override def toString: String = {
    "\n" + data.map(d => d.mkString(" | ")).mkString("\n")
  }


}

case class RMatrix (dim: Int, val data: Seq[Seq[Rational]]) extends Matrix[Rational] {
  //assert(data.length == dim)
  assert(data.forall(d => d.length == dim))

  def rows: Seq[Seq[Rational]] = data
  
}

class EMatrix private(dim: Int, val data: Seq[Seq[Expr]]) extends Matrix[Expr] {
  //assert(data.length == dim)
  assert(data.forall(d => d.length == dim))

  def map(f: Expr => Rational): RMatrix = {
    RMatrix(dim, data.map(row => {
      row.map(elem => f(elem))
      }))
  }
}