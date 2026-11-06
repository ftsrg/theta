// calloc(0, size) may return a unique non-null pointer, which free must accept.
void *calloc(unsigned long, unsigned long);
void free(void *);
void abort(void);

int main(void) {
  int *p = calloc(0, sizeof(int));
  if (!p) abort();
  free(p);
  return 0;
}
