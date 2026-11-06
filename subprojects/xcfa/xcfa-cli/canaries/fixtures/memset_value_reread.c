// the memset value is read once, before the first write
extern void *malloc(unsigned long);
extern void free(void *);
extern void *memset(void *, int, unsigned long);
extern void *memcpy(void *, const void *, unsigned long);
extern void *memmove(void *, const void *, unsigned long);
extern int __VERIFIER_nondet_int(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "fixture.c", 8, "reach_error"); }
int main() { char a[3]; a[0] = 1; memset(a, a[0] + 1, 3); if (a[1] != 2) reach_error(); return 0; }
