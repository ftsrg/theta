// `p ? p->f : d` must not dereference `p` when the guard is false. The branches' *statements* were
// already emitted under a guard, but both branch *values* ended up inside a single Ite, so a
// dereference in one of them became an unconditional memory access -- and the memsafety
// instrumentation then checked an access the program never performs, reporting a false
// `valid-deref` violation on one of the most common idioms in C.
//
// This is what `memsafety/test-0232-2` and `list-ext-properties/test-0232_1-2` trip on:
//   item->data = (item->next) ? item->next->data : malloc(sizeof *item);
// where `item->next` is legitimately NULL on the first append.
//
// The equivalent if/else never misreported, and the fix makes the conditional agree with it.
extern void abort(void);
void reach_error(){ abort(); }

struct S { struct S *next; int v; };

int main() {
  struct S a;
  a.next = 0;
  a.v = 1;
  struct S *p = &a;

  /* the guard is false, so the true branch's dereference must never happen */
  int x = (p->next) ? p->next->v : 42;
  if (x != 42) reach_error();

  /* and when the guard holds, the dereference is real and its value is used */
  a.next = &a;
  int y = (p->next) ? p->next->v : 99;
  if (y != 1) reach_error();

  /* nested, with the dereference in the false branch instead */
  a.next = 0;
  int z = (p->next == 0) ? 7 : p->next->v;
  if (z != 7) reach_error();

  return 0;
}
