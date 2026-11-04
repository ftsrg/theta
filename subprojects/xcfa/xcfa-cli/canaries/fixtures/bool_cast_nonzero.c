// Conversion to _Bool yields 1 for every non-zero value (C17 6.3.1.2), not the low bit.
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "bool_cast_nonzero.c", 3, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
int main() { int x = __VERIFIER_nondet_int(); if (x == 0) return 0; _Bool b = x; if (!b) reach_error(); _Bool c = (_Bool)2.5; if (!c) reach_error(); _Bool d = (_Bool)0.0; if (d) reach_error(); return 0; }
