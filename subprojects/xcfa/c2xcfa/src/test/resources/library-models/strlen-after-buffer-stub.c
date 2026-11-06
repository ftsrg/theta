// fgets fills one cell of the buffer and leaves the others stale, so strlen stays a stub.
extern char *fgets(char *s, int n, void *stream);
extern unsigned long strlen(const char *s);

int main() {
  char b[8] = {0};
  fgets(b, 8, 0);
  return (int)strlen(b) + 1;
}
