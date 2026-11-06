// A byte count that is no whole number of elements: 10 bytes hold two ints, so the third overruns.
int main() { int *p = (int *)__builtin_alloca(10UL); p[2] = 1; return 0; }
