// A copy of a freed pointer keeps its object: the access through it is a use after free.
void *malloc(unsigned long);
void free(void *);

int main(void) {
  int *p = malloc(8);
  if (!p) return 0;
  int *q = p;
  free(p);
  *q = 1;
  return 0;
}
