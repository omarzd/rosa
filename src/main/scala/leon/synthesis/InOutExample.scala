/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis

import purescala.Trees.Expr

class InExample(val ins: Seq[Expr])
class InOutExample(is: Seq[Expr], val outs: Seq[Expr]) extends InExample(is)
