#include<stdio.h>

int main()
  {
  double a, b, res, exact;

  exact = -0.827396059946821; /* −0. 827396059946821368141165095479816 */

  a = 77617.0;
  b = 33096.0;

  res = 333.75 * (b*b*b*b*b*b) + (a*a)*(11.0*a*a*b*b - b*b*b*b*b*b - 121.0*b*b*b*b -2.0) + 5.5*b*b*b*b*b*b*b*b + a/(2.0*b);

  printf("exact = %2.15f   and   res = %2.15f\n", exact, res);

  return 0;
  }