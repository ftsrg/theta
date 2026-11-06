// fgets with a symbolic size fills one cell of the buffer and leaves the others stale, so strlen
// stays a stub.
extern char *fgets(char *s, int n, void *stream);
extern unsigned long strlen(const char *s);
extern int __VERIFIER_nondet_int(void);

int main() {
  char b[8] = {0};
  int n = __VERIFIER_nondet_int();
  if (n < 1 || n > 8) return 0;
  fgets(b, n, 0);
  return (int)strlen(b) + 1;
}
