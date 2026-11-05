// Filling, copying, zero-allocating and growing whole int blocks stays in bounds.
#include <stdlib.h>
#include <string.h>
int main(void) {
  int *p = malloc(2 * sizeof(int));
  int *q = calloc(2, sizeof(int));
  if (!p || !q) {
    free(p);
    free(q);
    return 0;
  }
  memset(p, 0, 2 * sizeof(int));
  memcpy(q, p, 2 * sizeof(int));
  int *r = realloc(p, 3 * sizeof(int));
  if (!r) {
    free(p);
    free(q);
    return 0;
  }
  r[2] = q[1];
  free(r);
  free(q);
  return 0;
}
