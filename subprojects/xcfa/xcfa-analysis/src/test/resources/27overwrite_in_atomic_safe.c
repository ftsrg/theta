// A write overwritten later in its atomic unit cannot be read, neither in nor after the unit.
extern void reach_error(void);
extern void __VERIFIER_atomic_begin(void);
extern void __VERIFIER_atomic_end(void);
struct { unsigned v; } S;
int main(void) {
  __VERIFIER_atomic_begin();
  S.v = 1;
  S.v = 2;
  if (S.v != 2) reach_error();
  __VERIFIER_atomic_end();
  if (S.v != 2) reach_error();
  __VERIFIER_atomic_begin();
  S.v = 3;
  if (S.v != 3) reach_error();
  __VERIFIER_atomic_end();
  return 0;
}
