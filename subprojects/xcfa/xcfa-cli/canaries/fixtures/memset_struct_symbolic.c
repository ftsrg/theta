// memset of structs with a symbolic count is a loop under bytes, not a call left in place
extern void *malloc(unsigned long);
extern void free(void *);
extern void *memset(void *, int, unsigned long);
extern void *memcpy(void *, const void *, unsigned long);
extern void *memmove(void *, const void *, unsigned long);
extern int __VERIFIER_nondet_int(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "fixture.c", 8, "reach_error"); }
struct s { int x; int y; };
int main() { int n = __VERIFIER_nondet_int(); if (n < 1 || n > 4) return 0; struct s *p = malloc(n * sizeof(struct s)); if (!p) return 0;
  memset(p, 0, n * sizeof(struct s)); if (p[0].y == 0) reach_error(); return 0; }
