// A dereference guarded by `?:` is not checked on the branch where the pointer is NULL.
void *malloc(unsigned long);
void free(void *);

int main(void) {
  int *p = malloc(sizeof(int));
  if (p) *p = 0;
  int x = p ? *p : 1;
  free(p);
  return x;
}
