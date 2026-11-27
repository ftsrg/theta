// Single-threaded violation: thread_ids of its witness must be ignored.

extern int __VERIFIER_nondet_int(void);
void reach_error() {}

int main(void) {
    int x = __VERIFIER_nondet_int();
    if (x == 5) {
        reach_error();
    }
    return 0;
}
