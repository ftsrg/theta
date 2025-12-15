extern int __VERIFIER_nondet_int();

extern void reach_error();

int main() {
    int i = __VERIFIER_nondet_int();
    if (i > 0) {
        if (i < 2) {
            reach_error();
        }
    } 
    return 0;
}