// From the cir2c wiki (cases/theta-oob-mintest/oob.c): a constant-offset heap over-read, unsafe for
// valid-deref
#include <stdlib.h>
int main() {
  int* p = (int*)malloc(4 * sizeof(int));
  if (!p) return 0;
  p[0] = 1;
  int x = p[10];   /* out-of-bounds read: only 4 ints allocated */
  free(p);
  return x;
}
