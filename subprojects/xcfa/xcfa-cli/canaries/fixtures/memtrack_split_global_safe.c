// A global pointer once into the middle of the block is split under multi: at the exit it still
// points to the block, which is not lost.
#include <stdlib.h>
struct s {
  int a;
  int b;
};
int* g;
int main(void) {
  struct s* p = malloc(sizeof(struct s));
  if (!p) return 0;
  g = &p->b;
  g = &p->a;
  return 0;
}
