// The other end of the nondet fill: it must not write PAST the region it was given.
//
// Companion to nondet_memory_symbolic_size.c. `__VERIFIER_nondet_memory(g_buf, 1)` covers byte 0
// only, so byte 7 keeps the zero every global starts with and the error is unreachable. A loop
// whose bound is the object rather than the argument -- or one that rounds the count up past the
// region instead of only over a straddled cell -- makes this UNSAFE, which is the failure a
// fixture that only checks the written end would miss.
extern void abort(void);
void reach_error() { abort(); }
extern unsigned int __VERIFIER_nondet_uint(void);
extern void __VERIFIER_nondet_memory(void *mem, unsigned long size);

unsigned char g_buf[8];

int main() {
  unsigned int n = __VERIFIER_nondet_uint();
  if (n != 1) return 0;
  __VERIFIER_nondet_memory(g_buf, n);
  if (g_buf[7] == 0xAB) reach_error();
  return 0;
}
