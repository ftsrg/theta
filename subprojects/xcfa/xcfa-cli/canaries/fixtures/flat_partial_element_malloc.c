// malloc(10) bound to an `int *` holds two whole ints: the third (bytes 8..11) overruns the
// block. The recorded cell count rounds down to whole elements.
void *malloc(unsigned long);
void free(void *);

int main(void) {
  int *p = malloc(10);
  if (!p) return 0;
  p[1] = 1;
  p[2] = 2;
  free(p);
  return 0;
}
