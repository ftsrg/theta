// a terminated string passes the checks of a %s
extern void *malloc(unsigned long);
extern void free(void *);
extern int printf(const char *, ...);
int main() {
  char *p = malloc(4);
  if (!p) return 0;
  p[0] = 65;
  p[1] = 0;
  printf("%s\n", p);
  free(p);
  return 0;
}
