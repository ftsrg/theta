// the memcpy count is read once, before the first write
extern void *malloc(unsigned long);
extern void free(void *);
extern void *memset(void *, int, unsigned long);
extern void *memcpy(void *, const void *, unsigned long);
extern void *memmove(void *, const void *, unsigned long);
extern int __VERIFIER_nondet_int(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "fixture.c", 8, "reach_error"); }
int main() { char a[4], b[4]; a[0] = 1; a[1] = 2; a[2] = 3; a[3] = 4; b[0] = 4; int k = __VERIFIER_nondet_int(); if (k != 0) return 0;
  memcpy(b, a, b[k]); if (b[3] != 4) reach_error(); return 0; }
