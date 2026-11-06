// The last member of the last element of a malloc'd struct array is in bounds.
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
  s[0].a = 1;
  s[2].c = 2;
  s[2].b = 3;
  free(s);
  return 0;
}
