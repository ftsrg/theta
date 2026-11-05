// Eight bytes hold one long under LP64, so the second long overruns the block.
#include <stdlib.h>
int main(void) {
  long *s = malloc(2 * 4);
  if (!s) return 0;
  s[0] = 1;
  s[1] = 2;
  free(s);
  return 0;
}
