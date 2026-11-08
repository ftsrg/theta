// `%s` stores a word of the source string, which may be longer than the buffer. The stub does
// not model the source, so the overflow is not reported as certain.
#include <stdio.h>
extern char __VERIFIER_nondet_char(void);

int main(void) {
  char line[8];
  char alias[2];
  for (int i = 0; i < 7; i++) line[i] = __VERIFIER_nondet_char();
  line[7] = 0;
  if (sscanf(line, "%s", alias) == 1) {
    return alias[0];
  }
  return 0;
}
