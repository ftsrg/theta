// fgets is a stub that fills one cell, so the zeros after it are stale: in C the line can be long.
// strlen is not exact here, and the error path depends on its over-approximated value.
extern void abort(void);
extern char *fgets(char *s, int n, void *stream);
extern unsigned long strlen(const char *s);
void reach_error() { abort(); }

int main() {
  char buf[8] = {0};
  fgets(buf, 8, 0);
  if (strlen(buf) > 4) reach_error();
  return 0;
}
