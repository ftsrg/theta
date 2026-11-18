// Converting an integer that the signed target type cannot represent is implementation-defined,
// and GCC reduces it modulo 2^N; without --enable-signed-wraparound the value was kept.
extern void abort(void);
void reach_error() { abort(); }
extern long __VERIFIER_nondet_long(void);
typedef enum { VALUE = 0x8000000000000000 } enum_t;
enum_t get(void) { return VALUE; }
int main() {
  long l = __VERIFIER_nondet_long();
  if (l == 4294967301L && (int)l != 5) reach_error();
  if ((int)get() != 0) reach_error();
  signed char c = 200;
  if (c != -56) reach_error();
  unsigned long u = __VERIFIER_nondet_long();
  int x = u;
  if (x > 2147483647 || x < -2147483647 - 1) reach_error();
  return 0;
}
