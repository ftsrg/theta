// The loop writes only dead locals, but it is no busy wait under memory safety: a[i] is out of
// bounds in the fifth iteration, and that check is added after the loop is collapsed.
extern int __VERIFIER_nondet_int(void);
int a[4];
int main() {
  int x = __VERIFIER_nondet_int();
  int i = 0;
  while (x >= 0) {
    int t = a[i];
    i = i + 1;
  }
  return 0;
}
