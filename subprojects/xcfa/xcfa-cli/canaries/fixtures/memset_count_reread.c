// the memset count is read once, before the first write
extern void *malloc(unsigned long);
extern void free(void *);
extern void *memset(void *, int, unsigned long);
extern void *memcpy(void *, const void *, unsigned long);
extern void *memmove(void *, const void *, unsigned long);
extern int __VERIFIER_nondet_int(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "fixture.c", 8, "reach_error"); }
int main() { char a[4]; a[0] = 4; a[1] = 7; a[2] = 7; a[3] = 7; int k = __VERIFIER_nondet_int(); if (k != 0) return 0;
  memset(a, 0, a[k]); if (a[1] != 0) reach_error(); return 0; }
