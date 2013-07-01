/*
  Benchmark from http://www.cprover.org/cdfpl/

  "Numeric Bounds Analysis with Conflict-Driven Learning"

*/

import leon.Real
import Real._

object Sqrt {

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