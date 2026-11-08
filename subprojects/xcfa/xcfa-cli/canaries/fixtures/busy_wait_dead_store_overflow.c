// The loop writes only the dead local y, but it is no busy wait under no-overflow: y - 1
// overflows in the ninth iteration, and that check is added after the loop is collapsed.
extern int __VERIFIER_nondet_int(void);
int main() {
  int x = __VERIFIER_nondet_int();
  int y = -2147483640;
  while (x >= 0) {
    y = y - 1;
  }
  return 0;
}
