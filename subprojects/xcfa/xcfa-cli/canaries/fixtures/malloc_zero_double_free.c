// Freeing a block of size 0 twice is a double free.
void *malloc(unsigned long);
void free(void *);

int main(void) {
  char *p = malloc(0);
  if (!p) return 0;
  free(p);
  free(p);
  return 0;
}
