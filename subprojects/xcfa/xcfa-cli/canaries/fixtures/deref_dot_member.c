// `(*p).a` fell through to a cell read, so it came out as `(deref (deref p 0) 0)` -- field
// 0's *content* used as the object's base -- while the identical `p->a` and `p[0].a`, which
// both already had the "a struct's value is its base id" rule, came out right. With a
// nondet in field 0 that base is arbitrary, so valid-deref reported a bogus invalid
// dereference (memsafety-ext3/test22-1).
extern void abort(void);
extern int __VERIFIER_nondet_int(void);
void reach_error() { abort(); }

struct dummy {
  int a, b;
};
struct dummy d1;

int main() {
  d1.a = __VERIFIER_nondet_int();
  struct dummy *p = &d1;
  if ((*p).a != p->a || (*p).a != p[0].a) reach_error();
  (*p).b = 4;
  if (p->b != 4) reach_error();
  return 0;
}
