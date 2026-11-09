#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);

void *safe_malloc(unsigned int size) {
  void *p = malloc(size);
  if (p == 0) abort();
  return p;
}

int main(void) {
  int *a = safe_malloc(16);
  a[__VERIFIER_nondet_int()] = 1;
  return 0;
}
