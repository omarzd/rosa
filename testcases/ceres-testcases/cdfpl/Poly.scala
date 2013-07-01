import leon.Real
import Real._


object Poly {

  def poly(x: Real): Real = {
    require(x.in(0, 1))
    val y = (x-1)*(x-1)*(x-1)*(x-1)
    assert(y <= 0.5000001)
    x*x*x*x - 4*x*x*x + 6*x*x - 4*x + 1
  } ensuring(res => noise(res, 1e-9))

}

/*
int main(void)
{
  float x,y,z;

  x = __BUILTIN_DAED_FBETWEEN(0,1);
  y = (x-1)*(x-1)*(x-1)*(x-1);
  z = x*x*x*x - 4*x*x*x + 6*x*x - 4*x + 1;
}
*/