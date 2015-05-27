
#include <stdio.h>
#include <iostream>
#include <cstdlib>   // Include rand()
#include <chrono>
#include <math.h>

using namespace std;
using namespace std::chrono;

float jetFloat(float x1, float x2);
double jetDouble(double x1, double x2);

long float2Long(float f, int bits) {
  return (long) round(f * pow(2, bits));
}

int main() {

  int bound = 1000;
  

  high_resolution_clock::time_point t1 = high_resolution_clock::now();
  float res = 0.0f;
  int i = 0;
  while(i < bound) {
    res += jetFloat(3.4, -5.4);
    i++;
  }
  high_resolution_clock::time_point t2 = high_resolution_clock::now();
  duration<double> time_span = duration_cast<duration<double>>(t2 - t1);
  cout << "time float: " << time_span.count() << "\n";
 


  t1 = high_resolution_clock::now();
  double res2 = 0.0;
  i = 0;
  while(i < bound) {
    res2 += jetDouble(3.4, -5.4);
    i++;
  }
  t2 = high_resolution_clock::now();
  time_span = duration_cast<duration<double>>(t2 - t1);
  cout << "time double: " << time_span.count() << "\n";
 

  t1 = high_resolution_clock::now();
  long res2 = 0;
  i = 0;
  while(i < bound) {
    res2 += jetDouble(float2Long(3.4, ), -5.4);
    i++;
  }
  t2 = high_resolution_clock::now();
  time_span = duration_cast<duration<double>>(t2 - t1);
  cout << "time double: " << time_span.count() << "\n";
  

  return 0;
}

float jetFloat(float x1, float x2) {
  float t = (3*x1*x1 + 2*x2 - x1);

  return x1 + ((2*x1*(t/(x1*x1 + 1))*
    (t/(x1*x1 + 1) - 3) + x1*x1*(4*(t/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(t/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)));
}

double jetDouble(double x1, double x2) {
  double t = (3*x1*x1 + 2*x2 - x1);

  return x1 + ((2*x1*(t/(x1*x1 + 1))*
    (t/(x1*x1 + 1) - 3) + x1*x1*(4*(t/(x1*x1 + 1))-6))*
    (x1*x1 + 1) + 3*x1*x1*(t/(x1*x1 + 1)) + x1*x1*x1 + x1 +
    3*((3*x1*x1 + 2*x2 -x1)/(x1*x1 + 1)));
}