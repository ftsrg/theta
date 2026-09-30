extern void reach_error(void);
extern int __VERIFIER_nondet_int(void);

int main() {
  int i = -1;
  while (i != 0) {
    i--;
    i = (-1) * i;
    __VERIFIER_nondet_int();
  }
  reach_error();
  return 0;
}
