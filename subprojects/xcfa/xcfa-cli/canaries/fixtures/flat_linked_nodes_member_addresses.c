// Two malloc'd nodes linked through an inline member: the member addresses of distinct
// objects differ, and following a link lands on the other node's member. Each object gets its
// own address range, so `&a->link` and `&b->link` cannot coincide.
extern void abort(void);
void reach_error() { abort(); }
void *malloc(unsigned long);

struct lh { struct lh *next, *prev; };
struct node { int v; struct lh link; };

int main(void) {
  struct node *a = malloc(sizeof(*a)), *b = malloc(sizeof(*b));
  if (!a || !b) return 0;
  a->link.next = &b->link;
  b->link.prev = &a->link;
  a->link.prev = &a->link;
  b->link.next = &b->link;
  if (a->link.next == &a->link) reach_error();
  if (a->link.next->prev != &a->link) reach_error();
  if (&a->link == &b->link) reach_error();
  return 0;
}
