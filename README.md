rosa
====
The Real compiler

** Check the 'opt' branch with improved running times. **


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

Rosa is written as a fork of the [Leon verification framework](https://github.com/epfl-lara/leon);
this is why this repository contains more than just Rosa code.

Instructions for Linux and Mac OSX
-------------------------------------

### How to build ### 

Rosa is set up to work with sbt (simple-build-tool).
Once you have sbt installed on your machine, type the following in your favourite terminal
in Rosa's home directory:
$ sbt
> compile

### How to run ###

You can run Rosa directly from within sbt like this (after starting sbt):
> run [input files]

For command-line options:
> run --help


You can also run Rosa as a standalone script by first creating the script:
$ sbt script

Then you can run:
$ ./rosa [input files]

### libz3 or libscalaz3 not found ###

Depending on your system, the commands above may fail with a message that says
that some libz3 or libscalaz3 is missing (or a variation thereof).
Rosa uses ScalaZ3 for interfacing with the Z3 SMT solver, and this binding
may need to be recompiled for different platforms. Or the platform you are on
searches a different path than expected.

Rosa comes with precompiled libraries of ScalaZ3 and Z3 that have been tested
on my Linux and Mac OSX installations.
- Libraries for Linux are included in the unmanaged/64/scalaz3_2.10-2.1.jar.
If you get an error saying that libscalaz3 or libz3 are not found,
first try to extract these libraries from the .jar file and move them for instance
to Rosa's home directory or whenever you think the JVM searches.

- Libraries for OSX are included directly in the Rosa's home directory, since
this is where my Mac searches by default. If you get an error saying that libscalaz3 
or libz3 are not found, try to move them to whatever folder you think the JVM searches.

- If Rosa should crash on one of the existing examples in testcases/reals,
then check if you have installed Z3 on machine. If so, try to uninstall it,
as Rosa may not play well with recent versions of Z3. If not, let me know about this issue.

- If the above does not work, you can try to recompile ScalaZ3 on your machine.
You will find the instructions on ScalaZ3's github page (https://github.com/epfl-lara/ScalaZ3).
Do not get the most recent Z3 version, instead use the one provided in resources/.

### no DirectedRounding in java.library.path ###

Precompiled libraries are available in /lib.

Check below for how to 

Installation instructions for Windows
-------------------------------------
1. install gcc
2. install java development kit (JDK)
   http://www.oracle.com/technetwork/java/javase/downloads/index.html
3. add javac to the system path:
   C:\Program Files\Java\jdk1.8.0\bin
4. install sbt
   http://www.scala-sbt.org/download.html
5. fork+clone rosa from github
6. fork+clone ScalaZ3 from github  (only the lib-bin folder is needed)
7. start the Git Shell
8. go to the rosa folder
9. type "cmd" to start a windows shell with the correct paths.
   - type "build" to build the libs for windows (using build.bat)
   - type "exit" to leave the windows shell
10. type "sbt". this will start the sbt console.
11. type "run"


### Existing examples ###

To run the most recent benchmarks (for example):

> run testcases/real/techreport/Straightline.scala
> run testcases/real/techreport/Discontinuity.scala
> run testcases/real/techreport/Pendulum.scala


### Native library functions ###
Rosa itself uses two native libraries. They come pre-compiled for Mac and Linux, but in case you need re-compiling,
here's how.

The project uses JNI to access some low-level system functions that the JVM merrily ignores (e.g. directed rounding).
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


