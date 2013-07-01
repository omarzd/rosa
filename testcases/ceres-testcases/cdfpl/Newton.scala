
import leon.Real
import Real._

object Newton {

  def f(x: Real): Real = {
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  }

  def fp(x: Real): Real = {
    1 - (x*x)/2.0 + (x*x*x*x)/24.0 + (x*x*x*x*x*x)/720.0
  }

  /*
    VAL = 0.2, 0.4, 0.6, 0.8, 1.0, 1.2, 1.4, 2.0
    default 3 iterations
  */
  def newton(in: Real): Real = {
    require(in > -0.2 && in < 0.2)

    val x1 = in - f(in)/fp(in)

    val x2 = x1 - f(x1)/fp(x1)
    val x3 = x2 - f(x2)/fp(x2)

    x3
  } ensuring(res => ~res < 0.1)
}


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
*/