// `alloca` is declared by glibc's <stdlib.h>, but theta's model of that header did not
// carry it, so every task that calls it after including <stdlib.h> died in the frontend
// with "No such variable or macro: alloca" -- the whole array-memsafety `*-alloca-*`
// family. The lowering has always been there (AllocaFunctionPass); only the declaration
// was missing.
#include <stdlib.h>
extern void abort(void);
extern int __VERIFIER_nondet_int(void);
void reach_error() { abort(); }

int main() {
  int n = __VERIFIER_nondet_int();
  if (n < 1 || n > 4) n = 1;
  int *a = alloca(n * sizeof(int));
  a[0] = 7;
  if (a[0] != 7) reach_error();
  return 0;
}
