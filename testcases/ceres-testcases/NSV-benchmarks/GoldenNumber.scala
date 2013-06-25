import leon.Real
import Real._

import leon.Utils._


object GoldenNumber {

  #include <math.h>

int main(void)
{ 
  float t;
  int i,n;
  t=1;
  // n in [1,1000]
  for (i=1; i<=n; i++) {
    t=t*(sqrt(5)-1)/2;
    t = FPRINT(t);
  } 
  FPRINT(t);
}


#include <math.h>

int main(void)
{ 
  float x,y,z;
  int i,n;
  x=1;
  y=(sqrt(5)-1)/2;
  // n in [1,1000]
  for (i=1;i<=n;i++) 
  {
    z=x;
    x=y;
    y=z-y;
  } 
}

}