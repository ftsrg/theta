// A block allocated through a void pointer wrapper is bounded in elements.
extern void *malloc(unsigned long); extern void free(void *); extern void abort(void); void *m(unsigned long n){ void *p = malloc(n); if (!p) abort(); return p; } int main(void){ int *a = (int *)m(4 * sizeof(int)); a[4] = 1; free(a); return 0; }
