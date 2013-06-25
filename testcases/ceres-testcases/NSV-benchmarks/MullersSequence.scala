#include<stdio.h>

/* Muller suite: three fixed points: 3, 5 and 100    */
/* 3 and 5 are repulsive, 100 is attractive          */
/* roundoff errors when computing the first terms    */
/* induce a change from a trajectory converging to 5 */
/* to a trajectory converging to 100.                */

int main()
  {
  double xnm1, xn, xnp1;
  int i, fin;

  xnm1=4.0;
  xn=4.25;
  printf("Enter the final index: ");
  scanf("%d", &fin);

  for (i=2; i<= fin; i++)
    {
    xnp1 = 108.0 - (815.0 - 1500.0/xnm1)/xn;
    xnm1 = xn;
    xn = xnp1;
    printf("x[%d] = %f\n", i, xnp1);
    }

  /* printf("x[%d] = %f\n", fin, xnp1); */

  return 0;
  }