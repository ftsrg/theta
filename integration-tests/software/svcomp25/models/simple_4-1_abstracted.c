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
void reach_error() { __assert_fail("0", "simple_4-1_abstracted.c", 3, "reach_error"); }

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}

int main(void) {
  unsigned int x = 0x0ffffff1;

  // START CONSTANTEXTRAPOLATION
  if (x > (1)) {
    long long int x__VERIFIER_LA_tmp0;
    x__VERIFIER_LA_tmp0 = x;
    long long int __VERIFIER_LA_iterations0;
    __VERIFIER_LA_iterations0 = ((x__VERIFIER_LA_tmp0 - 1) / 2L) + 1L;
    unsigned int x__VERIFIER_LA_old_tmp0;
    x__VERIFIER_LA_old_tmp0 = x;
    x = (__VERIFIER_LA_iterations0 * -2L) + x__VERIFIER_LA_old_tmp0;
  }
  // END CONSTANTEXTRAPOLATION

  __VERIFIER_assert(!(x % 2));
}
