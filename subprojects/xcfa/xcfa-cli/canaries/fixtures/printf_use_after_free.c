// printf reads the string of a %s, so a freed one is invalid
extern void *malloc(unsigned long);
extern void free(void *);
extern int printf(const char *, ...);
int main() {
  char *p = malloc(4);
  if (!p) return 0;
  p[0] = 0;
  free(p);
  printf("%s\n", p);
  return 0;
}
