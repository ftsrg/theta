// C11 6.7.6.2p5: a variably-modified type's size "shall evaluate to a value greater than
// zero", so a VLA sized from an unconstrained nondet is undefined when that size is 0 --
// sv-benchmarks files it under valid-deref. Nothing could see it: the object was simply
// given size 0, every `for (i = 0; i < n; i++)` ran zero times, so no dereference happened
// at all and no access guard could fire. Seven `loops/` tasks are exactly this shape and
// theta proved every one of them safe.
extern unsigned int __VERIFIER_nondet_uint(void);

int main() {
  unsigned int n = __VERIFIER_nondet_uint();
  int a[n]; // n may be 0
  return 0;
}
