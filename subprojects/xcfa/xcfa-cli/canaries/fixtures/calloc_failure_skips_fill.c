// A failed calloc returns NULL, and the zero-fill it is lowered to must not write through it.
extern void *calloc(unsigned long, unsigned long);
extern void free(void *);

int main() {
  int *p = (int *)calloc(4, sizeof(int));
  if (p) free(p);
  return 0;
}
