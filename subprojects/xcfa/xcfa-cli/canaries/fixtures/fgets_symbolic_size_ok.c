// `fgets` into the rest of a block, with a symbolic size that fits it: no overflow.
#include <stdio.h>
#include <stdlib.h>
extern unsigned long __VERIFIER_nondet_ulong(void);

int main(void) {
  char *buf = malloc(300);
  if (buf == NULL) return 0;
  unsigned long off = __VERIFIER_nondet_ulong();
  if (off >= 300) {
    free(buf);
    return 0;
  }
  if (fgets(buf + off, (int)(300 - off), stdin) != NULL) buf[0] = 1;
  free(buf);
  return 0;
}
