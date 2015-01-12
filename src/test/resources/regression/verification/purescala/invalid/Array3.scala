/* Copyright 2009-2015 EPFL, Lausanne */

import leon.lang._

object Test {

  def find(c: Array[Int], i: Int): Int = {
    if(c(i) == i)
      42
    else
      12
  } ensuring(_ > 0)

}
