// A non-null block of size 0 has no accessible byte.
void *malloc(unsigned long);
void free(void *);

int main(void) {
  char *p = malloc(0);
  if (!p) return 0;
  p[0] = 1;
  free(p);
  return 0;
}
