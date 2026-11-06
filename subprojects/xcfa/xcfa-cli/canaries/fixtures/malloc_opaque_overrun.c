// A block whose type cannot be recovered is still bounded exactly.
extern void* malloc(unsigned long);
extern void free(void*);
extern void abort(void);
void* m(unsigned long n) {
  void* p = malloc(n);
  if (!p)
    abort();
  return p;
}
void init(void* v) {
  int* x = v;
  x[4] = 1;
}
int main(void) {
  void* p = m(4 * sizeof(int));
  init(p);
  free(p);
  return 0;
}
