// The snprintf stub returns any int, but in C `n` is 2. An overflow that needs a large `n` may
// not exist in C, so the verdict is withheld.
extern int snprintf(char *s, unsigned long n, const char *format, ...);

int main() {
  char b[4];
  int n = snprintf(b, 4, "%s", "ab");
  if (n > 100) {
    return n + 2147483647;
  }
  return 0;
}
