// Every element of a block allocated through a `void *` wrapper is in bounds.
#include <stdlib.h>
void* safe_malloc(unsigned int size) {
  void* p = malloc(size);
  if (p == 0)
    abort();
  return p;
}
int main(void) {
  int* a = (int*)safe_malloc(4 * sizeof(int));
  for (int i = 0; i < 4; i++)
    a[i] = i;
  free(a);
  return 0;
}
