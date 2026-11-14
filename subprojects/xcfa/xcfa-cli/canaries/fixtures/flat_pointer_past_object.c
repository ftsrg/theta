// Under the flat model `b` starts right after `a`'s slot, so `p[3]` through a pointer to `a` is an
// address inside `b`, which the slot check accepted. The access leaves `p`'s own object.
int a[2], b[2];

int main(void) {
  int *p = a;
  return p[3];
}
