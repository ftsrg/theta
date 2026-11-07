// A wrapper used at two types gets each block sized in bytes.
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
  int* a = m(4 * sizeof(int));
  char* c = m(5);
  a[3] = 1;
  c[4] = 1;
  free(a);
  free(c);
  return 0;
}
