// `&s.u` of a union member is the member's base, for a global and a local struct alike.
extern void abort(void);
void reach_error(void) { abort(); }
union U { int a; char c[4]; };
struct S { int k; union U u; int t; } g;
int main(void) {
  union U *p = &g.u;
  p->a = 7;
  struct S s = {0};
  union U *q = &s.u;
  q->a = 8;
  if (g.u.a != 7 || g.k != 0 || g.t != 0 || s.u.a != 8 || s.k != 0 || s.t != 0) reach_error();
  return 0;
}
