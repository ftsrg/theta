int power(volatile int base, volatile int exp) {
    if(exp == 0) return 1;
    return power(base, exp - 1) * exp;
}

int main() {
    int a = __VERIFIER_NONDET_INT();
    int b = __VERIFIER_NONDET_INT();
    return power(a, b);
}