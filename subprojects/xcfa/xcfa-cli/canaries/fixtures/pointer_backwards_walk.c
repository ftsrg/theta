// A pointer step is counted in the pointer-sized *unsigned* type, so `p--` reaches
// ReferenceElimination as `&*(p + 4294967295)` under ILP32. Under bitvector arithmetic that
// is exactly `p - 1`, because the addition wraps by construction. Under *integer*
// arithmetic the operands are unbounded, nothing wrapped, and one `p--` left the offset
// 2^32 too large -- so `MemsafetyPass`'s `ptr_size[base] <= offset` reported a bogus invalid
// dereference on the very next read. Every backwards walk over a buffer was a false
// valid-deref alarm (the `cmemrchr` idiom: array-memsafety/openbsd_cmemrchr-alloca-2).
// The sibling `m--` in the same loop was always correct -- the frontend wrapped that one.
#include <stdlib.h>
extern void abort(void);
extern char __VERIFIER_nondet_char(void);
void reach_error() { abort(); }

int main() {
  char *a = (char *)alloca(3 * sizeof(char));
  for (int i = 0; i < 3; i++) a[i] = __VERIFIER_nondet_char();
  a[0] = 4;

  unsigned char *cp = (unsigned char *)a + 2; // walk backwards, ending exactly at a[0]
  size_t m = 3;
  while (1) {
    if (*cp == 7) break;
    if (--m == 0) break;
    --cp;
  }
  if (m == 0 && *cp != 4) reach_error(); // the walk ended on a[0], which holds 4
  return 0;
}
