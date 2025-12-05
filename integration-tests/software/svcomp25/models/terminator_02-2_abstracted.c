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
void reach_error() { __assert_fail("0", "terminator_02-2_abstracted.c", 3, "reach_error"); }

extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
int __VERIFIER_nondet_int();
_Bool __VERIFIER_nondet_bool();

int main()
{
    int x=__VERIFIER_nondet_int();
    int z=__VERIFIER_nondet_int();
    if (!(x>-100)) return 0;
    if (!(x<200)) return 0;
    if (!(z>100)) return 0;
    if (!(z<200)) return 0;
    // START HAVOCABSTRACTION
    if ((z > (100)) & (x < (100))) {
    z = __VERIFIER_nondet_int();
    x = __VERIFIER_nondet_int();
    }
    if ((z > (100)) & (x < (100))) abort();
    // END HAVOCABSTRACTION                       

    __VERIFIER_assert(x>=100 || z<=100);

    return 0;
}


