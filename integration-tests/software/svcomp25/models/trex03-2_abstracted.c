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
void reach_error() { __assert_fail("0", "trex03-2_abstracted.c", 3, "reach_error"); }

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
unsigned int __VERIFIER_nondet_uint();
_Bool __VERIFIER_nondet_bool();

int main()
{
  unsigned int x1=__VERIFIER_nondet_uint(), x2=__VERIFIER_nondet_uint(), x3=__VERIFIER_nondet_uint();
  unsigned int d1=1, d2=1, d3=1;
  _Bool c1=__VERIFIER_nondet_bool(), c2=__VERIFIER_nondet_bool();
  
  // START HAVOCABSTRACTION
  if ((x3 > (0)) & ((x2 > (0)) & (x1 > (0)))) {
  x3 = __VERIFIER_nondet_uint();
  x2 = __VERIFIER_nondet_uint();
  x1 = __VERIFIER_nondet_uint();
  c2 = __VERIFIER_nondet_bool();
  c1 = __VERIFIER_nondet_bool();
  }
  if ((x3 > (0)) & ((x2 > (0)) & (x1 > (0)))) abort();
  // END HAVOCABSTRACTION

  __VERIFIER_assert(x1==0 || x2==0 || x3==0);
  return 0;
}

