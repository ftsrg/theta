// A variable is range-constrained where it is havoc'd; a memory *cell* never was. Under
// integer arithmetic a cell is an unbounded Int, so an unwritten one read back as any
// integer at all -- not merely as any `unsigned char`. The difference of two char-sized
// cells is in [-255,255] and its negation cannot overflow, but the model could not see that
// and reported an overflow: five known no-overflow false alarms, including
// termination-memory-alloca/openbsd_cstrncmp-alloca-1 (a regression in run 84) and
// dirname-1. Stated as an assume, not a cast: castTo is a *no-op for signed* narrow types
// unless --enable-signed-wraparound is set, so it would fix `unsigned char` and silently
// miss `char`.
#include <stdlib.h>

int main() {
  unsigned char *u = (unsigned char *)alloca(2);
  signed char *s = (signed char *)alloca(2);
  int ru = (int)u[0] - (int)u[1]; // in [-255, 255]
  int rs = (int)s[0] - (int)s[1]; // in [-255, 255] for signed char too
  return (-ru) + (-rs);           // so neither negation can overflow
}
