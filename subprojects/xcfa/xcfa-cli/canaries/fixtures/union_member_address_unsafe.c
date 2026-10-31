// Planted bug: a write through `&s.u` is visible through the union's other member.
extern void abort(void);
void reach_error(void) { abort(); }
union U { int a; char c[4]; };
struct S { int k; union U u; int t; } s;
int main(void) {
  union U *p = &s.u;
  p->a = 7;
  if (s.u.c[0] == 7) reach_error();
  return 0;
}
