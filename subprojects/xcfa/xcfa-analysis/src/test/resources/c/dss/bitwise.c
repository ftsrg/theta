extern int __VERIFIER_nondet_int(void);
void reach_error() {}

int main() {
  unsigned int x = 5;
  while (__VERIFIER_nondet_int()) {
    x += 8;
  }
  if ((x & 5) != 5) {
    reach_error();
  }
  return 0;
}
