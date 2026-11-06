// fgets with a symbolic size is a stub that fills one cell, so the zeros after it are stale: in C
// the line can be long. strlen is not exact here, and the error path depends on its
// over-approximated value.
extern void abort(void);
extern char *fgets(char *s, int n, void *stream);
extern unsigned long strlen(const char *s);
extern int __VERIFIER_nondet_int(void);
void reach_error() { abort(); }

int main() {
  char buf[8] = {0};
  int n = __VERIFIER_nondet_int();
  if (n < 1 || n > 8) return 0;
  fgets(buf, n, 0);
  if (strlen(buf) > 4) reach_error();
  return 0;
}
