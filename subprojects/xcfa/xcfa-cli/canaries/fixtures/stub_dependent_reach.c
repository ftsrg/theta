// The snprintf stub returns any int, but in C `n` is 2, so reach_error is not reachable.
extern void abort(void);
extern int snprintf(char *s, unsigned long n, const char *format, ...);
void reach_error() { abort(); }

int main() {
  char b[4];
  int n = snprintf(b, 4, "%s", "ab");
  if (n == 7) reach_error();
  return 0;
}
