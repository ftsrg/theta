#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);

int main(void) {
  int *p = malloc(16);
  if (p) p[__VERIFIER_nondet_int()] = 1;
  return 0;
}
