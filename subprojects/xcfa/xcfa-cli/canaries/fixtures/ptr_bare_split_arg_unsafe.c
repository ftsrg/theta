extern void reach_error(void);
extern int __VERIFIER_nondet_int(void);
typedef struct {
  int v;
} C;
void w(C* c, int x) {
  c->v = x;
}
int main(void) {
  C a[3];
  a[0].v = 0;
  a[1].v = 0;
  a[2].v = 0;
  int i = __VERIFIER_nondet_int();
  if (i < 1 || i > 2)
    return 0;
  C* p;
  p = &a[i];
  w(p, 5);
  if (a[i].v == 5)
    reach_error();
  return 0;
}
