// Under bytes, a wide access is in bounds only if all of its bytes are: the int at bytes 8..11
// and the char at byte 11 of a 12-byte block are fine (the overrun case is
// flat_partial_element_malloc.c).
#include <stdlib.h>

int main(void) {
  int *p = malloc(12);
  if (!p) return 0;
  p[2] = 3;
  char *c = (char *)p;
  c[11] = 4;
  free(p);
  return 0;
}
