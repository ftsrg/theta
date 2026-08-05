// The same lifetime, one iteration at a time: each pass through the body declares a *new*
// object, so writing through the previous iteration's array is a use-after-scope
// (memsafety-ext3/derefInLoop1). The model already gave each unrolled iteration its own
// base -- what it never did was retire the old one, which is why the existing
// `ptr_size[base] <= index` guard could not fire.
extern void abort(void);
void reach_error() { abort(); }

int main() {
  int *p = 0;
  for (int i = 0; i < 2; i++) {
    int a[10];
    if (i == 0) p = a;
    else p[0] = 1; // iteration 1 writes through iteration 0's dead array
  }
  return 0;
}
