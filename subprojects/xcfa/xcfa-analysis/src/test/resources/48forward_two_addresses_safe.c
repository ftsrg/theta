// As 47forward_two_addresses_unsafe.c, but neither cell holds the value the error needs.
extern int __VERIFIER_nondet_int(void);
extern void reach_error(void);

int a[3];

int main(void) {
  int i = __VERIFIER_nondet_int() ? 0 : 2;
  a[0] = 1;
  a[2] = 5;
  a[1] = 9;
  if (a[i] == 9) reach_error();
  return 0;
}
