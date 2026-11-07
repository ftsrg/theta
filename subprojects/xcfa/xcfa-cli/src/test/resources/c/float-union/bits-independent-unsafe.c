// The error path writes a double through a union but does not use its bits, so the
// over-approximated bits cannot make the counterexample spurious. Expected: unsafe.
extern void abort(void);
void reach_error() { abort(); }
extern int __VERIFIER_nondet_int(void);
typedef unsigned int u32;
typedef union {
  double value;
  struct {
    u32 lsw;
    u32 msw;
  } parts;
} shape;

int main() {
  shape u;
  u.value = 1.0;
  int k = __VERIFIER_nondet_int();
  if (k == 7) reach_error();
  return u.parts.msw == 0;
}
