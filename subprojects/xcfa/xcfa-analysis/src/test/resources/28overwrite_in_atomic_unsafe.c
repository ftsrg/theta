// Reading before the write of its own atomic unit sees the previous unit's write.
extern void reach_error(void);
extern void __VERIFIER_atomic_begin(void);
extern void __VERIFIER_atomic_end(void);
struct { unsigned v; } S;
int main(void) {
  S.v = 1;
  __VERIFIER_atomic_begin();
  if (S.v == 1) reach_error();
  S.v = 2;
  __VERIFIER_atomic_end();
  return 0;
}
