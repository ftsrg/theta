// A VLA of symbolic length, then a call whose local has its address taken: the local is allocated
// after the whole VLA, so writing the VLA's last element cannot reach it.
extern void abort(void);
void reach_error() { abort(); }
extern int __VERIFIER_nondet_int(void);

void inner(int *vla, int n) {
  int z = 3;
  int *pz = &z;
  vla[n - 1] = 9;
  if (*pz != 3) reach_error();
}

int main(void) {
  int n = __VERIFIER_nondet_int();
  if (n <= 0 || n > 1000000) return 0;
  int vla[n];
  inner(vla, n);
  return 0;
}
