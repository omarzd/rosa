import leon.Real
import Real._


/*
  Benchmarks used in the paper
    Static Analysis of Finite Precision Computations, Eric Goubault and Sylvie Putot

  */
object VMCAI2011 {

  def f {
    /*int main(int N) {
  double E, E0, E1, S0, S1, S;
  double A1, A2, A3;
  double B1, B2;
  int i;
  A1 = DBETWEEN(0.5, 0.8);
  A2 = DBETWEEN(-1.5,-1);
  A3 = DBETWEEN(0.8,1.3);
  B1 = DBETWEEN(1.39,1.41);
  B2 = DBETWEEN(-0.71,-0.69);
  E=DBETWEEN(0,1.0);
  E0=DBETWEEN(0,1.0);
  for (i=1;i<=N;i++) {
    E1 = E0;
    E0 = E;
    E = DBETWEEN(0,1.0);
    S1 = S0;
    S0 = S;
    S = A1 * E + E0 * A2 + E1 * A3 + S0 * B1 + S1 * B2 ;
    DPRINT(S);
  }
  DSENSITIVITY(S);
  return 0;
  }*/
  }

  def g {
    // Skipping, uses matrices
  }

  def h {
    /*#include <math.h>
#define _EPS        0.00000001   /* 10^-8 */
int main ()
{   
    double xn, xnp1, residu, Input, Output, should_be_zero;
    int i;
    Input = __BUILTIN_DAED_FBETWEEN(16.0,16.1); 
    xn = 1.0/Input; xnp1 = xn;    
    residu = 2.0*_EPS*(xn+xnp1)/(xn+xnp1);
    i = 0;
    while (fabs(residu) > _EPS) { 
      xnp1 = xn * (1.875 + Input*xn*xn*(-1.25+0.375*Input*xn*xn));
      residu = 2.0*(xnp1-xn)/(xn+xnp1);
      xn = xnp1;
      i++;
    }
    Output = 1.0 / xnp1; 
    should_be_zero = Output-sqrt(Input);
    return 0;
}*/
  }

  def k {
    /*
    int main(void)
{
  float x0, x1, x2;
  int i;
  int n;

  n = IBETWEEN(100,100);
  x0 = 11/2.0;
  x1 = 61/11.0;

  for (i=1 ; i<=n ; i++)
  {  
    x2 = 111 - (1130 - 3000/x0) / x1;
    x0 = x1;
    x1 = x2; 
    FPRINT(x1);
   }
}*/
  }

  def p {
   /* int main(void)
{
  float x,y,z,t;

  x = FBETWEEN(0,1);
  y = (x-1)*(x-1)*(x-1)*(x-1);
  z = x*x;
  z = z*z - 4*x*z + 6*z - 4*x + 1;
  t = z-y;
  FSENSITIVITY(z);
  FSENSITIVITY(t);
}*/
  }

  def r {
/*
int main(){
  double f;
  double x = 77617;
  double y = 33096;

  f = 333.75*y*y*y*y*y*y;
  f += x*x*(11*x*x*y*y - y*y*y*y*y*y - 121*y*y*y*y - 2);
  f += 5.5*y*y*y*y*y*y*y*y;
  f += x / (2*y);

  printf("Result is %f\n",f);

  return 0;
}*/
  }

}