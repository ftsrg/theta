// The result is bound to a void pointer, so its cell count is unknown: the frontend has to
// retry under the bytes model instead of bounding the block by its byte count.
#include <stdlib.h>

int main() {
  void *q = malloc(2 * sizeof(int));
  int *p = q;
  if (p == 0) return 0;
  p[2] = 1;
  free(p);
  return 0;
}
