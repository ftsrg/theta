// `(unsigned long)&((T *)0)->f` is a member offset, not the address of an object: it does not
// make a Safe verdict unreliable as a converted object address does.
#include <stdlib.h>
struct list_head { struct list_head *next, *prev; };
struct node { int value; struct list_head link; };

int main(void) {
  struct node *n = malloc(sizeof(struct node));
  if (!n) return 0;
  n->value = 1;
  struct list_head *l = &n->link;
  struct node *m =
    (struct node *)((char *)l - (unsigned long)(&((struct node *)0)->link));
  int v = m->value;
  free(n);
  return v - 1;
}
