#include <math.h>

void main() {
  double x, y, resx, resy, res;
  // x in [1,2]
  // y in [0.1,0.2]
  resx = y/x;
  resx = 1.0/(sqrt(1.0+resx*resx));
  resy = x/y;
  resy = 1.0/(sqrt(resy*resy+1.0));
  res = resx*resx+resy*resy;
}