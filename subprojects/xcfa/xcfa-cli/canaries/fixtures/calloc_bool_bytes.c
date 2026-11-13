// calloc zeroes every byte, and a `_Bool` lives in a byte: under the byte-addressed model a `_Bool`
// cell kept apart from the bytes that memset wrote read an unconstrained value.
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "calloc_bool_bytes.c", 6, "reach_error"); }
#include <stdlib.h>
int main() {
  _Bool *flags = calloc(2, sizeof(_Bool));
  if (!flags) return 0;
  if (flags[1]) reach_error();
  flags[0] = 1;
  if (((unsigned char *)flags)[0] != 1) reach_error();
  return 0;
}
