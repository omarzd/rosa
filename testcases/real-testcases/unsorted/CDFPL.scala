import leon.Real
import Real._

/*
  CDFPL benchmarks:

http://www.cprover.org/cdfpl/

Paper: Numeric Bounds Analysis with Conflict-Driven Learning

also used in
Refining abstract interpretation based value analysis with constraint programming techniques
*/
object CDFPL {
  def f(x: Real): Real = {
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  }

  def fp(x: Real): Real = {
    1 - (x*x)/2.0 + (x*x*x*x)/24.0 + (x*x*x*x*x*x)/720.0
  }


  def newton1(in: Real): Real = {
    require(in > -0.2 && in < 0.2)
    val x1 = in - f(in)/fp(in)
    val x2 = x1 - f(x1)/fp(x1)
    val x3 = x2 - f(x2)/fp(x2)
    x3
  } ensuring(res => ~res < 0.1)

  def newton2(in: Real): Real = {
    require(in > -0.4 && in < 0.4)
    val x1 = in - f(in)/fp(in)
    val x2 = x1 - f(x1)/fp(x1)
    val x3 = x2 - f(x2)/fp(x2)
    x3
  } ensuring(res => ~res < 0.1)

  def newton3(in: Real): Real = {
    require(in > -0.6 && in < 0.6)
    val x1 = in - f(in)/fp(in)
    val x2 = x1 - f(x1)/fp(x1)
    val x3 = x2 - f(x2)/fp(x2)
    x3
  } ensuring(res => ~res < 0.1)

  def newton4(in: Real): Real = {
    require(in > -0.8 && in < 0.8)
    val x1 = in - f(in)/fp(in)
    val x2 = x1 - f(x1)/fp(x1)
    val x3 = x2 - f(x2)/fp(x2)
    x3
  } ensuring(res => ~res < 0.1)

  def newton5(in: Real): Real = {
    require(in > -1.0 && in < 1.0)
    val x1 = in - f(in)/fp(in)
    val x2 = x1 - f(x1)/fp(x1)
    val x3 = x2 - f(x2)/fp(x2)
    x3
  } ensuring(res => ~res < 0.1)

  def newton6(in: Real): Real = {
    require(in > -1.2 && in < 1.2)
    val x1 = in - f(in)/fp(in)
    val x2 = x1 - f(x1)/fp(x1)
    val x3 = x2 - f(x2)/fp(x2)
    x3
  } ensuring(res => ~res < 0.1)

  def newton7(in: Real): Real = {
    require(in > -1.4 && in < 1.4)
    val x1 = in - f(in)/fp(in)
    val x2 = x1 - f(x1)/fp(x1)
    val x3 = x2 - f(x2)/fp(x2)
    x3
  } ensuring(res => ~res < 0.1)

  def newton8(in: Real): Real = {
    require(in > -2.0 && in < 2.0)
    val x1 = in - f(in)/fp(in)
    val x2 = x1 - f(x1)/fp(x1)
    val x3 = x2 - f(x2)/fp(x2)
    x3
  } ensuring(res => ~res < 0.1)


def poly(x: Real): Real = {
    require(x.in(0, 1))
    val y = (x-1)*(x-1)*(x-1)*(x-1)
    assert(y <= 0.5000001)
    x*x*x*x - 4*x*x*x + 6*x*x - 4*x + 1
  } ensuring(res => noise(res, 1e-9))

}
def sine1(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring(res => ~res <= 0.99 && ~res >= -0.99)

  def sine2(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring(res => ~res <= 1.0 && ~res >= -1.0)

  def sine3(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring(res => ~res <= 1.001 && ~res >= -1.001)

  def sine4(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring(res => ~res <= 1.01 && ~res >= -1.01)

  def sine5(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring(res => ~res <= 1.1 && ~res >= -1.1)

  def sine6(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring(res => ~res <= 1.2 && ~res >= -1.2)

  def sine7(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring(res => ~res <= 1.5 && ~res >= -1.5)

  def sine8(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring(res => ~res <= 2.0 && ~res >= -2.0)
}

def sqroot1(x: Real): Real = {
    require(x >= 0.0 && x < 1.0)
    1.0 + 0.5*x - 0.125*x*x + 0.0625*x*x*x - 0.0390625*x*x*x*x
  } ensuring(res => ~res >= 0.0 && ~res < 1.39)

  def sqroot2(x: Real): Real = {
    require(x >= 0.0 && x < 1.0)
    1.0 + 0.5*x - 0.125*x*x + 0.0625*x*x*x - 0.0390625*x*x*x*x
  } ensuring(res => ~res >= 0.0 && ~res < 1.398)

  def sqroot3(x: Real): Real = {
    require(x >= 0.0 && x < 1.0)
    1.0 + 0.5*x - 0.125*x*x + 0.0625*x*x*x - 0.0390625*x*x*x*x
  } ensuring(res => ~res >= 0.0 && ~res < 1.39843)

  def sqroot4(x: Real): Real = {
    require(x >= 0.0 && x < 1.0)
    1.0 + 0.5*x - 0.125*x*x + 0.0625*x*x*x - 0.0390625*x*x*x*x
  } ensuring(res => ~res >= 0.0 && ~res < 1.39844)

  def sqroot5(x: Real): Real = {
    require(x >= 0.0 && x < 1.0)
    1.0 + 0.5*x - 0.125*x*x + 0.0625*x*x*x - 0.0390625*x*x*x*x
  } ensuring(res => ~res >= 0.0 && ~res < 1.3985)

  def sqroot6(x: Real): Real = {
    require(x >= 0.0 && x < 1.0)
    1.0 + 0.5*x - 0.125*x*x + 0.0625*x*x*x - 0.0390625*x*x*x*x
  } ensuring(res => ~res >= 0.0 && ~res < 1.399)

  def sqroot7(x: Real): Real = {
    require(x >= 0.0 && x < 1.0)
    1.0 + 0.5*x - 0.125*x*x + 0.0625*x*x*x - 0.0390625*x*x*x*x
  } ensuring(res => ~res >= 0.0 && ~res < 1.4)

  def sqroot1(x: Real): Real = {
    require(x >= 0.0 && x < 1.0)
    1.0 + 0.5*x - 0.125*x*x + 0.0625*x*x*x - 0.0390625*x*x*x*x
  } ensuring(res => ~res >= 0.0 && ~res < 1.5)

}

/*
//APPROXIMATES sqroot(1+x)

#ifndef NR
#error PLEASE DEFINE THE NR OF THE BENCHMARK (FLAG -DNR=[1,8])
#endif


#if NR == 1
#define VAL 1.39f
#elif NR == 2
#define VAL 1.398f
#elif NR == 3
#define VAL 1.39843f
#elif NR == 4
#define VAL 1.39844f
#elif NR == 5
#define VAL 1.3985f
#elif NR == 6
#define VAL 1.399f
#elif NR == 7
#define VAL 1.4f
#elif NR == 8
#define VAL 1.5f
#endif

int main()
{
  float IN;
  __CPROVER_assume(IN >= 0.0f && IN < 1.0f);

  float x = IN;

  float result =
    1f + 0.5f*x - 0.125f*x*x + 0.0625f*x*x*x - 0.0390625f*x*x*x*x;

  assert(result >= 0.0f && result < VAL);

  return 0;
}
*/

/*#define HALFPI 1.57079632679f

#ifndef NR
#error PLEASE DEFINE THE NR OF THE BENCHMARK (FLAG -DNR=[1,8])
#endif


#if NR == 1
#define VAL 0.99
#elif NR == 2
#define VAL 1.0f
#elif NR == 3
#define VAL 1.001f
#elif NR == 4
#define VAL 1.01f
#elif NR == 5
#define VAL 1.1f
#elif NR == 6
#define VAL 1.2f
#elif NR == 7
#define VAL 1.5f
#elif NR == 8
#define VAL 2.0f
#endif

int main()
{
  float IN;
  __CPROVER_assume(IN > -HALFPI && IN < HALFPI);

  float x = IN;

  float result = x - (x*x*x)/6.0f + (x*x*x*x*x)/120.0f + (x*x*x*x*x*x*x)/5040.0f;

  assert(result <= VAL && result >= -VAL);

  return 0;
}*/

/*
int main(void)
{
  float x,y,z;

  x = __BUILTIN_DAED_FBETWEEN(0,1);
  y = (x-1)*(x-1)*(x-1)*(x-1);
  z = x*x*x*x - 4*x*x*x + 6*x*x - 4*x + 1;
}
*/



/*
ORIGINAL:

#include <stdio.h>

#ifndef NR
//#error PLEASE DEFINE THE NR OF THE BENCHMARK (FLAG -DNR=[1,8])
#endif

#if NR == 1
#define VAL 0.2f
#elif NR == 2
#define VAL 0.4f
#elif NR == 3
#define VAL 0.6f
#elif NR == 4
#define VAL 0.8f
#elif NR == 5
#define VAL 1.0f
#elif NR == 6
#define VAL 1.2f
#elif NR == 7
#define VAL 1.4f
#elif NR == 8
#define VAL 2.0f
#endif

#ifndef ITERATIONS
#error please set number of iterations (between 2 and 3)
#endif

#if !(ITERATIONS >= 1 && ITERATIONS <= 3)
#error Number of iterations must be between 1 and 3
#endif

float f(float x)
{
  return x - (x*x*x)/6.0f + (x*x*x*x*x)/120.0f + (x*x*x*x*x*x*x)/5040.0f;
}

float fp(float x)
{
  return 1 - (x*x)/2.0f + (x*x*x*x)/24.0f + (x*x*x*x*x*x)/720.0f;
}

int main()
{
  float IN;
  __CPROVER_assume(IN > -VAL && IN < VAL);

  float x = IN - f(IN)/fp(IN);
#if ITERATIONS > 1
  x = x - f(x)/fp(x);
#if ITERATIONS > 2
  x = x - f(x)/fp(x);
#endif
#endif

  assert(x < 0.1);

  return 0;
}

}