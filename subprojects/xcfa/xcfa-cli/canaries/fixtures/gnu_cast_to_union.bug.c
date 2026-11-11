// The .bug twin of gnu_cast_to_union.c.
extern void abort(void);
void reach_error() { abort(); }
extern int __VERIFIER_nondet_int(void);
typedef union { int i; double d; } u_t;
int main() {
  int x = __VERIFIER_nondet_int();
  u_t a = (u_t)x;
  if (a.i == 5) reach_error();
  return 0;
}
