// A negative index that leaves the object is still an invalid dereference.
#include <stdlib.h>
int main() {
  int *b = malloc(2 * sizeof(int));
  if (!b) return 0;
  b[0] = 7;
  b[1] = 8;
  int *p = b + 1;
  int k = -2;
  int x = p[k];
  free(b);
  return x;
}
