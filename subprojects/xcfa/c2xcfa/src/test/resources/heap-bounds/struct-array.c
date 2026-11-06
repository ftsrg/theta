#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);

struct item {
  int a;
  long b;
  char c;
};

int main(void) {
  struct item *s = malloc(3 * sizeof(struct item));
  if (s) s[__VERIFIER_nondet_int()].c = 1;
  return 0;
}
