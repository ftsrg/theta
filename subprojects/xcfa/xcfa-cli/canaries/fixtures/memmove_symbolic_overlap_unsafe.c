// memmove with a symbolic count copies through an overlap
extern void *malloc(unsigned long);
extern void free(void *);
extern void *memset(void *, int, unsigned long);
extern void *memcpy(void *, const void *, unsigned long);
extern void *memmove(void *, const void *, unsigned long);
extern int __VERIFIER_nondet_int(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "fixture.c", 8, "reach_error"); }
int main() { char a[4]; a[0] = 1; a[1] = 2; a[2] = 3; a[3] = 4; int n = __VERIFIER_nondet_int(); if (n != 2) return 0;
  memmove(a + 1, a, n); if (a[2] == 2) reach_error(); return 0; }
