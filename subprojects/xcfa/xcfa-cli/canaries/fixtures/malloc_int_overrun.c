// a malloc bound is in cells: the fourth int of a 3-int block overruns it
extern void *malloc(unsigned long);
extern void free(void *);
extern void *memset(void *, int, unsigned long);
extern void *memcpy(void *, const void *, unsigned long);
extern void *memmove(void *, const void *, unsigned long);
extern int __VERIFIER_nondet_int(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "fixture.c", 8, "reach_error"); }
int main() { int *p = (int *)malloc(3 * sizeof(int)); if (!p) return 0; p[3] = 1; free(p); return 0; }
