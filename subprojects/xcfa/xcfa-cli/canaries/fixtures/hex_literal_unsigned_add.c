// An unsuffixed hex constant that does not fit in int is unsigned int (C11 6.4.4.1p5), so the
// addition below is unsigned and cannot overflow. Typing every hex constant as int reported one.
extern int __VERIFIER_nondet_int(void);
int main() {
  int i = __VERIFIER_nondet_int();
  if (i > 0) {
    unsigned int r = i + 0x80000000;
    return r > 5u ? 0 : 1;
  }
  return 0;
}
