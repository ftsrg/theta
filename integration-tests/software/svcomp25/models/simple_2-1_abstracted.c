extern void abort(void);
extern int __VERIFIER_nondet_int();
extern _Bool __VERIFIER_nondet_bool();
extern char __VERIFIER_nondet_char();
extern double __VERIFIER_nondet_double();
extern float __VERIFIER_nondet_float();
extern unsigned long __VERIFIER_nondet_ulong();
extern unsigned long long __VERIFIER_nondet_ulonglong();
extern unsigned int __VERIFIER_nondet_uint();
extern int __VERIFIER_nondet_int();
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "simple_2-1_abstracted.c", 3, "reach_error"); }
extern unsigned int __VERIFIER_nondet_uint(void);

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}

int main(void) {
  unsigned int x = __VERIFIER_nondet_uint();

  // START HAVOCABSTRACTION
  if (x < (268435455)) {
  x = __VERIFIER_nondet_uint();
  }
  if (x < (268435455)) abort();
  // END HAVOCABSTRACTION

  __VERIFIER_assert(x >= 0x0fffffff);
}
