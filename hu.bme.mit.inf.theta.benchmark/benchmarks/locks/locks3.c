extern int __VERIFIER_nondet_int();

int main()
{
    int p1 = __VERIFIER_nondet_int();  // condition variable
    int lk1; // lock variable

    int cond;

    while(1) {
        cond = __VERIFIER_nondet_int();
        if (cond == 0) {
            return 0;
        } else {}
        lk1 = 0; // initially lock is open


    // lock phase
        if (p1 != 0) {
            lk1 = 1; // acquire lock
        } else {}


    // unlock phase
        if (p1 != 0) {
            if (lk1 != 1) assert(0); // assertion failure
            lk1 = 0;
        } else {}

    }

    return 0;
}
