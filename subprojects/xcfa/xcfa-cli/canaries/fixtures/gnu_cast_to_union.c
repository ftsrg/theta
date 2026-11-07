// GNU cast to union: the member of the operand's type holds the operand (int, double, pointer).
extern void abort(void);
void reach_error() { abort(); }
extern int __VERIFIER_nondet_int(void);
typedef union { int i; double d; int *p; } u_t;
int g;
int get_i(u_t u) { return u.i; }
int main() {
  int x = __VERIFIER_nondet_int();
  u_t a = (u_t)x;
  if (a.i != x) reach_error();
  if (get_i((u_t)(x + 1)) != x + 1) reach_error();
  u_t b = (u_t)2.5;
  if (b.d != 2.5) reach_error();
  u_t c = (u_t)&g;
  *c.p = 7;
  if (g != 7) reach_error();
  for (int k = 0; k < 3; k++) {
    u_t e = (u_t)k;
    if (e.i != k) reach_error();
  }
  return 0;
}
