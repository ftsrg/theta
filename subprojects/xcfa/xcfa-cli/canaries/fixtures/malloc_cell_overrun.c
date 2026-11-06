// A dereference offset counts cells, so the size recorded for a malloc'd block has to be in
// cells too. The byte count let p[2] .. p[7] of a two-int block through.
#include <stdlib.h>

int main() {
  int *p = malloc(2 * sizeof(int));
  if (p == 0) return 0;
  p[2] = 1;
  free(p);
  return 0;
}
