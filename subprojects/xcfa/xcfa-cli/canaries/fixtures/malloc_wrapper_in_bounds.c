// The last element of a block from a void pointer wrapper is in bounds.
extern void* malloc(unsigned long);
extern void free(void*);
extern void abort(void);
void* m(unsigned long n) {
  void* p = malloc(n);
  if (!p)
    abort();
  return p;
}
int main(void) {
  int* a = (int*)m(4 * sizeof(int));
  a[3] = 1;
  free(a);
  return 0;
}
