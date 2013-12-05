rosa
====

The Real compiler

Rosa let's you write your code in `Real`s like this (note the specification!):

    def rigidBodyControl1(x1: Real, x2: Real, x3: Real): Real = {
      require (-15 <= x1 && x1 <= 15 && -15 <= x2 && x2 <= 15 && -15 <= x3 && x3 <= 15) 
      -x1*x2 - 2*x2*x3 - x1 - x3
    } ensuring (res => res <= 705.0 && res +/- 6e-13)

and compiles this into:

    def rigidBodyControl1(x1: Double, x2: Double, x3: Double): Double = {
      -x1*x2 - 2*x2*x3 - x1 - x3
    }  

or 
    
    def rigidBodyControl1FixedPoint(x1: Int, x2: Int, x3: Int): Int = {
      val tmp0 = -(x1)
      val tmp1 = ((tmp0 * x2) >> 15)
      val tmp2 = ((16384l * x2) >> 14)
      val tmp3 = ((tmp2 * x3) >> 15)
      val tmp4 = ((tmp1 - (tmp3 << 1)) >> 2)
      val tmp5 = (((tmp4 << 6) - x1) >> 6)
      (((tmp5 << 6) - x3) >> 6)
    }

depending on which precision on the result you need (`6e-13` vs `0.163`).

Rosa is written as part of the [Leon verification framework](https://github.com/epfl-lara/leon);
this is why this repository contains more than just Rosa code.

### Compiling ###









### Running rosa ###





### Running the produced program ###
