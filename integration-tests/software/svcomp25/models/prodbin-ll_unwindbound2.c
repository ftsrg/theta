/* shift_add algorithm for computing the 
   product of two natural numbers
   
   This task is incorrect, here is an explanation why:
   - The first assertion z + x * y == (long long) a * b is a loop invariant, so it can never be violated.
   - Therefore a possible counterexample has to violate the assertion __VERIFIER_assert(z == (long long) a * b); after the loop.
   - However we need to execute the loop completely, because the condition !(y != 0) together with the loop invariant implies the second assertion.
   - Therefore y must always be greater than zero.
   - y is divided by 2 in every iteration, therefore b >= 2^1 (since b is the initial value of y).
   - Therefore we can find a counterexample.
*/
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "prodbin-ll.c", 14, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
void __VERIFIER_assert(int cond) {
    if (!(cond)) {
    ERROR:
        {reach_error();}
    }
    return;
}

int counter = 0;
int main() {
    int a, b;
    long long x, y, z;

    a = __VERIFIER_nondet_int();
    b = __VERIFIER_nondet_int();
    assume_abort_if_not(b >= 1);

    x = a;
    y = b;
    z = 0;

    while (counter++<2) {
        __VERIFIER_assert(z + x * y == (long long) a * b);
        if (!(y != 0))
            break;

        if (y % 2 == 1) {
            z = z + x;
            y = y - 1;
        }
        x = 2 * x;
        y = y / 2;
    }
    __VERIFIER_assert(z == (long long) a * b);
    
    return 0;
}
