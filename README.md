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


For command-line options,
    
    $ rosa --help

### Running testcases ###

To run the most recent benchmarks:

> run --silent --specGen --lipschitz testcases/real/techreport/Straightline.scala
> run --silent --specGen testcases/real/techreport/Discontinuity.scala


### Native library functions ###
Rosa itself uses two native libraries. They come pre-compiled for Mac and Linux, but in case you need re-compiling,
here's how.

The project uses JNI to access some low-level system functions that the JVM merrily ignores (for directed rounding).
The source code is located in `resources/` (`ceres_common_DirectedRounding.c`, `ceres_common_DirectedRounding.h`).
Whatever command you use, the new library MUST be named "libDirectedRounding".

Something like this works on Ubuntu:

    gcc -shared -I/usr/lib/jvm/java-6-sun-1.6.0.20/include -I/usr/lib/jvm/java-6-sun-1.6.0.20/include/linux
      -o libDirectedRounding.so ceres_common_DirectedRounding.c

And this worked on a Mac:

    gcc -m64 -I/System/Library/Frameworks/JavaVM.framework/Headers -c ceres_common_DirectedRounding.c
    gcc -m64 -dynamiclib -o libDirectedRounding.jnilib ceres_common_DirectedRounding.o

The other dependency is Z3, which Rosa interfaces through the ScalaZ3 project. If you need to recompile
ScalaZ3, please check the github page: https://github.com/epfl-lara/ScalaZ3.

Finally, the generated code can use the QuadDouble data type.
The QuadDouble quadruple double precision type is based on a C++ library from
http://crd-legacy.lbl.gov/~dhbailey/mpdist/

In order to use the type QuadDouble from Scala, you need to download and build
this library.  Then, you compile the provided JNI interface (also in `resources/`) for your architecture.

To compile on Linux:

    g++ -fPIC -I/usr/lib/jvm/java-6-sun-1.6.0.26/include/
      -I/usr/lib/jvm/java-6-sun-1.6.0.26/include/linux/ -I/home/edarulov/share/qd/include
      -c ceres_common_QuadDoubleInterface.cpp

    g++ -shared -o libQuadDouble.so ceres_common_QuadDoubleInterface.o ~/share/qd/src/*.o

