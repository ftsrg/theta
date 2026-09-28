// A struct- or array-typed member is an object of its own whose base id the parent's cell holds,
// so `&p->tail` is that id, not the address of the cell. Taking the cell's address makes the
// list below read as broken and `(*pa)[1]` write `s.z`.
extern void abort(void);
void reach_error() { abort(); }

struct node {
  struct node *next;
  struct node *prev;
};
struct list {
  struct node head;
  struct node tail;
};
struct S {
  int a[3];
  int z;
};

int main() {
  struct list l;
  struct list *list = &l;
  list->head.next = &list->tail;
  list->tail.prev = &l.head;
  struct node *h = &list->head;
  if (h->next->prev != h || h->next != &l.tail) reach_error();

  struct S s = {{1, 2, 3}, 7};
  struct S *p = &s;
  int (*pa)[3] = &p->a;
  (*pa)[1] = 5;
  if (s.a[1] != 5 || s.z != 7) reach_error();
  return 0;
}
