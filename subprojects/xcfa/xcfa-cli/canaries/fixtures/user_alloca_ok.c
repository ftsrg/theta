// Every element of a byte-sized `alloca` block is in bounds.
extern void *alloca(unsigned long);
int main(void) {
  int *a = alloca(4 * sizeof(int));
  for (int i = 0; i < 4; i++) a[i] = i;
  return a[3] - 3;
}
