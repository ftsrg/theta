// A block reached only through `void *` has no element type to count cells by: the program is
// rebuilt under bytes, which bounds the third int (bytes 8..11) of an 8-byte block exactly.
#include <stdlib.h>
int main(void) {
  void *v = malloc(8);
  if (!v) return 0;
  ((int *)v)[1] = 1;
  ((int *)v)[2] = 2;
  free(v);
  return 0;
}
