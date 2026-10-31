// A struct- or array-typed field keeps only the base of the member's own storage, so `&s.in`
// is that base, not the address of the field's cell (#602).
extern void abort(void);
void reach_error() { abort(); }

struct Inner {
  int x;
};
struct Outer {
  int pad;
  struct Inner in;
  int a[2];
};

struct Outer g = {3, {0}, {5, 6}};

int main() {
  struct Inner *p = &g.in;
  if (p->x != 0) reach_error();
  if (__atomic_exchange_n(&p->x, 1, 5) != 0 || g.in.x != 1 || g.pad != 3) reach_error();

  struct Outer *pg = &g;
  struct Inner *q = &pg->in;
  q->x = 7;
  if (g.in.x != 7 || p != q) reach_error();

  int (*row)[2] = &g.a;
  if ((*row)[1] != 6) reach_error();

  struct Outer l;
  l.pad = 4;
  l.in.x = 8;
  struct Inner *r = &l.in;
  if (r->x != 8 || l.pad != 4) reach_error();
  return 0;
}
