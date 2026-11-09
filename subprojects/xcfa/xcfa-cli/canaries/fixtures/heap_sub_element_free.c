// A 2-byte block bound to an int pointer holds no whole int, yet it is live and may be freed.
#include <stdlib.h>
int main(void) {
  int* p = malloc(2);
  if (!p)
    return 0;
  free(p);
  return 0;
}
