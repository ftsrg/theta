// The block comes from a wrapper that returns `void *`: its cells come from the caller's binding.
#include <stdlib.h>
void* safe_malloc(unsigned int size) {
  void* p = malloc(size);
  if (p == 0)
    abort();
  return p;
}
int main(void) {
  int* a = (int*)safe_malloc(4 * sizeof(int));
  a[3] = 3;
  a[4] = 4;
  return 0;
}
