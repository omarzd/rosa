/*
These benchmarks are inspired from the 
FEVS - Functional Equivalence Verification Suite
vsl.cis.udel.edu/fevs
*/


// Jacobi iteration scheme to solve the 2d Laplace equation
object Laplace {
  val epsilon: Double = ???
  val nx = 10
  val ny = 10

  def initdata: Array[Array[Double]] {

    val array = Array.fill[ny,nx](0.0)
    for (col <- 0 until nx) {
      new(0)(col) = 10 
      old(0)(col) = 10
      new(ny-1)(col) = 10
      old(ny-1)(col) = 10
    }
    array
  }

  def jacobi(old: Array[Array[Double]], error: Double): Array[Array[Double]] {
    int row, col, time;

    if (error >= epsilon) {
      var err = 0.0
      val new = Array.fill[ny, nx](0.0)
      for (row <- 1 until ny-1) {
        for (col <- 1 until nx-1) {
          val newRowCol = (old(row-1)(col)+old(row+1)(col)+ old(row)(col-1)+old(row)(col+1))*0.25;
          err += (old(row)(col) - new(row)(col)) * (old(row)(col) - new(row)(col))
          new(row)(col) = newRowCol
      }
      jacobi(new, err)
    } else {
      current
    }

  }
}


}

/*
#include <stdlib.h>
#include <stdio.h>
#define SQUARE(x) ((x)*(x))

#define nx   10    // number of x coordinates (including boundary)
#define ny   10    // number of rows including boundary
#define EPSILON 0.000001  // total error tolerance

double u1[ny][nx];
double u2[ny][nx];
double (*old)[nx] = u1;
double (*new)[nx] = u2;

void initdata();
void jacobi();
void print_frame(int, double (*grid)[nx]);

int main(int argc,char *argv[]) {
  initdata();
  print_frame(0, old);
  jacobi(EPSILON);
  return 0;
}

void jacobi(double epsilon) {
  double error = epsilon;
  int row, col, time;
  double (*tmp)[nx];

  time = 0;
  while (error >= epsilon) {
    for (error=0.0, row = 1; row < ny-1; row++) {
      for (col = 1; col < nx-1; col++) {
  new[row][col] = (old[row-1][col]+old[row+1][col]+
       old[row][col-1]+old[row][col+1])*0.25;
  error += SQUARE(old[row][col] - new[row][col]);
      }
    }
    time++;
    print_frame(time, new);
    printf("Current error at time %d is %2.5f\n\n", time, error);
    tmp = new; new = old; old = tmp;
  }
}

void initdata() {
  int row, col;

  for (row = 1; row < ny-1; row++)
    for (col = 1; col < nx-1; col++)
      new[row][col] = old[row][col] = 0;
  for (col = 0; col < nx; col++) {
    new[0][col] = old[0][col] = 10;
    new[ny-1][col] = old[ny-1][col] = 10;
  }
  printf("nx    = %d\n", nx);
  printf("ny    = %d\n", ny);
  printf("epsilon = %2.5f\n", EPSILON);
  printf("\n\n\n");
  fflush(stdout);
}

void print_frame(int time, double (*grid)[nx]) {
  int row, col;

  printf("\n\ntime=%d:\n\n", time);
  printf("\n");
  printf("   +");
  for (col = 0; col < nx; col++) printf("--------");
  printf("+\n");
  for (row = ny-1; row >=0; row--) {
    printf("%3d|", row);
    for (col = 0; col < nx; col++) printf("%8.2f", grid[row][col]);
    printf("|%3d", row);
    printf("\n");
  }
  printf("   +");
  for (col = 0; col < nx; col++) printf("--------");
  printf("+\n");
  printf("\n");
  fflush(stdout);
}*/