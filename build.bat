:: github for windows does not handle symbolic links
copy unmanaged\common\*.jar unmanaged\64
:: Do this if you have your own copy of libz3
:: copy "%HOME%\Downloads\z3-4.3.0-x64\bin\libz3.dll" .
:: Do this if you have rebuilt ScalaZ3
:: copy ..\..\ScalaZ3\target\scala-2.10\scalaz3_2.10-2.1.jar unmanaged\64
copy ..\..\ScalaZ3\lib-bin\*.dll .

set JDK="c:\Program Files\Java\jdk1.8.0_31"
:: on Windows, the JNI DLL name should not have a "lib" prefix
gcc -shared -I%JDK%\include -I%JDK%\include\win32 -o DirectedRounding.dll resources\ceres_common_DirectedRounding.c

