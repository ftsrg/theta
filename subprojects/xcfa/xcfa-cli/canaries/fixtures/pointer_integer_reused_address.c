// A new block may get the address of a freed one, so the two integers may be equal and `x` is
// then freed twice. Allocations never reuse an address in the model: no Safe verdict.
#include <stdlib.h>
typedef long intptr_t;

int main(void) {
  int *y = malloc(sizeof(int));
  if (y == 0) return 0;
  intptr_t a = (intptr_t)y;
  free(y);
  int *x = malloc(sizeof(int));
  if (x == 0) return 0;
  if ((intptr_t)x == a) {
    free(x);
  }
  free(x);
  return 0;
}
