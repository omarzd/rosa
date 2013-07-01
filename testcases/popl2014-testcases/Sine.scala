/*
  Benchmark from http://www.cprover.org/cdfpl/

  "Numeric Bounds Analysis with Conflict-Driven Learning"
*/

import leon.Real
import Real._

object Sine {

  // false
  def sine1(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring(res => ~res <= 0.99 && ~res >= -0.99)

  // false
  def sine2(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring(res => ~res <= 1.0 && ~res >= -1.0)

  // false
  def sine3(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring(res => ~res <= 1.001 && ~res >= -1.001)

  // true
  def sine4(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring(res => ~res <= 1.01 && ~res >= -1.01)

  // true
  def sine5(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring(res => ~res <= 1.1 && ~res >= -1.1)

  // true
  def sine6(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring(res => ~res <= 1.2 && ~res >= -1.2)

  // true
  def sine7(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring(res => ~res <= 1.5 && ~res >= -1.5)

  // true
  def sine8(x: Real): Real = {
    require(x > -1.57079632679 && x < 1.57079632679)
    x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0
  } ensuring(res => ~res <= 2.0 && ~res >= -2.0)
}

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