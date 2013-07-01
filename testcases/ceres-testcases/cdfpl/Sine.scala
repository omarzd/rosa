
import leon.Real
import Real._

object Sine {

  def sine(in: Real): Real = {
    require(in > -1.57079632679 && in < 1.57079632679)

    val x = in

    val result = x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 + (x*x*x*x*x*x*x)/5040.0

    result
  } ensuring(res => ~res <= 0.99 && ~res >= -0.99)

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