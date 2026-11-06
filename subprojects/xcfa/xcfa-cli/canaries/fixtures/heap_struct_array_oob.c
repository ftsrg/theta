// A struct array of three elements is bounded by its elements' cells: the fourth overruns it.
#include <stdlib.h>
struct item {
  int a;
  long b;
  char c;
};
int main(void) {
  struct item* s = malloc(3 * sizeof(struct item));
  if (!s)
    return 0;
  s[2].c = 2;
  s[3].a = 1;
  free(s);
  return 0;
}
