/* Copyright 2013 EPFL, Lausanne */

package leon
package real


object Utils {

  def formatOption[T](o: Option[T]): String = o match {
    case Some(x) => x.toString
    case None => " -- "
  }

}