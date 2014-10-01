

//Symbolic Robustness Analysis, R. Majumdar, I. Saha
OUTPUT int pressure1, pressure2;
int data_table[8][2] =
{ {10, 29}, {25, 29}, {30, 41}, {40, 63}, {60, 109}, {70, 127}, {80, 127}, {100, 127} };

int out1_table[4][2] =
{ {1, 0}, {2, 0}, {3, 1}, {4, 1} };


int out2_table[4][2] =
{ {1, 0}, {2, 0}, {3, 0}, {4, 1} };



def lookup1_2d(int *table_address, int xval): Int = {
  var index;

  if (xval < 17) index = 1
  else if ((xval >= 17) && (xval < 27)) index = 3;
  else if ((xval >= 27) && (xval < 35)) index = 5;
  else if ((xval >= 35) && (xval < 50)) index = 7;
  else if ((xval >= 50) && (xval < 65)) index = 9;
  else if ((xval >= 65) && (xval < 75)) index = 11;
  else if ((xval >= 75) && (xval < 90)) index = 13;
  else index = 15;

  val yval = *(table_address + index)
  return yval;
}

def lookup2_2d(int *table_address, int xval): Int {
  int index;

  if (xval == 1) index = 1;
  else if (xval == 2) index = 3;
  else if (xval == 3) index = 5;
  else if (xval == 4) index = 7;
  val yval = *(table_address + index)
  return yval;
}

def calc_trans_slow_torques(int angle, int speed): (Int, Int) {
  int val1, val3, val4;
  int gear;
  val val1 = lookup1_2d(&(data_table[0][0]), angle);
  if( 3 * speed <= val1) {
    gear = 3
  } else {
    gear = 4
  }

  val val3 = lookup2_2d(&(out1_table[0][0]), gear)
  pressure1 = val3 * 1000;
  val val4 = lookup2_2d(&(out2_table[0][0]), gear)
  pressure2 = val4 * 1000;
  (pressure1, pressure2)
}