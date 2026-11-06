// A label inside a statement of the switch body gets no guard: refuse instead of dropping it.
extern int __VERIFIER_nondet_int(void);

int main(void) {
  int r = __VERIFIER_nondet_int();
  int h = 0;
  switch (r) {
  case 1: {
    h = 1;
  case 2:
    h = 2;
  }
  }
  return h;
}
