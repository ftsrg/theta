// A block of four ints is bounded by four cells, not by its 16 bytes: index 4 is past its end.
#include <stdlib.h>
int main(void) {
  int* p = malloc(4 * sizeof(int));
  if (!p)
    return 0;
  p[3] = 3;
  p[4] = 4;
  free(p);
  return 0;
}
