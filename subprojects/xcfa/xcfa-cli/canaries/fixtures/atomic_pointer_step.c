// GCC's __atomic_* add/sub step a pointer by bytes, as if it were a uintptr_t, while C11's
// atomic_fetch_add/sub step it by elements. The GCC step was taken as an element count.
#include <stdatomic.h>
extern void abort(void);
void reach_error() { abort(); }

struct pair { int a, b; };

int main() {
  int a[4] = {10, 11, 12, 13};
  int *p = &a[0];
  int *old = __atomic_fetch_add(&p, sizeof(int), 5);
  if (old != &a[0] || p != &a[1] || *p != 11) reach_error();
  if (__atomic_add_fetch(&p, 2 * sizeof(int), 5) != &a[3]) reach_error();
  long back = -(long)sizeof(int);
  __atomic_fetch_add(&p, back, 5);
  if (*p != 12) reach_error();
  if (__atomic_sub_fetch(&p, 2 * sizeof(int), 5) != &a[0]) reach_error();

  struct pair s[3] = {{1, 2}, {3, 4}, {5, 6}};
  struct pair *q = &s[0];
  __atomic_fetch_add(&q, sizeof(struct pair), 5);
  if (q != &s[1] || q->b != 4) reach_error();

  char buf[8];
  void *v = buf;
  __atomic_fetch_add(&v, 3, 5); // void * steps by bytes (GNU)
  if (v != buf + 3) reach_error();

  _Atomic(int *) c = &a[0];
  atomic_fetch_add(&c, 3);
  if (*c != 13) reach_error();
  atomic_fetch_sub_explicit(&c, 2, memory_order_relaxed);
  if (c != &a[1]) reach_error();
  return 0;
}
