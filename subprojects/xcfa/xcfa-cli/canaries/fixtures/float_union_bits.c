// The newlib idiom: a double's IEEE bits through a union. Expected: safe.
extern void abort(void);
extern double __VERIFIER_nondet_double(void);
void reach_error() { abort(); }
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
  if (u.parts.msw != 0x3FF00000u || u.parts.lsw != 0u) reach_error();
  u.value = -2.0;
  if (u.parts.msw != 0xC0000000u) reach_error();
  double x = __VERIFIER_nondet_double();
  if (x != x) return 0;
  u.value = x;
  u.parts.msw &= 0x7FFFFFFFu; // clearing the sign bit is fabs
  double ax = u.value;
  if (ax != (x < 0 ? -x : x)) reach_error();
  return 0;
}
