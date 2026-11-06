// A struct element spans one cell per scalar member: s[1].a is past a one-struct block.
#include <stdlib.h>

struct S {
  int a;
  int b;
};

int main() {
  struct S *s = malloc(sizeof(struct S));
  if (s == 0) return 0;
  s->b = 1;
  s[1].a = 1;
  free(s);
  return 0;
}
