// A block first held in a void pointer is bounded in elements.
extern void *malloc(unsigned long); extern void free(void *); extern void abort(void); void *m(unsigned long n){ void *p = malloc(n); if (!p) abort(); return p; } int main(void){ void *v = malloc(4 * sizeof(int)); if (!v) abort(); int *a = v; a[4] = 1; free(a); return 0; }
