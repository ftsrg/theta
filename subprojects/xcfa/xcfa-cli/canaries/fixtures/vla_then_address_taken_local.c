// A VLA of symbolic length, then two nested calls whose locals have their address taken: every
// such local is allocated after the whole VLA, so writing the VLA's last element cannot reach
// one. VLAs and address-taken locals used to come from separate fixed-stride counters, so a long
// enough VLA overlapped the locals of frames pushed after it.
extern void abort(void);
void reach_error() { abort(); }
extern int __VERIFIER_nondet_int(void);

void inner(int *vla, int n) {
  int z = 3;
  int *pz = &z;
  vla[n - 1] = 9;
  if (*pz != 3) reach_error();
}

void outer(int *vla, int n) {
  int y = 1;
  int *py = &y;
  inner(vla, n);
  if (*py != 1) reach_error();
}

int main(void) {
  int n = __VERIFIER_nondet_int();
  if (n <= 0 || n > 1000000) return 0;
  int vla[n];
  outer(vla, n);
  return 0;
}
