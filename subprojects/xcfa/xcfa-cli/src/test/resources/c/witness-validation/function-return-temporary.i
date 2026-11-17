// The results of calls inside larger expressions are havoced into frontend temporaries.

extern unsigned short __VERIFIER_nondet_ushort(void);
void reach_error() {}

int main(void) {
    unsigned short m = 3;
    unsigned short a = __VERIFIER_nondet_ushort() & m;
    unsigned short b;
    b = __VERIFIER_nondet_ushort() & m;
    if (a == 1 && b == 2) {
        reach_error();
    }
    return 0;
}
