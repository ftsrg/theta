// The overflow needs scanf to succeed, which it can, so the verdict does not depend on a stub.
extern int scanf(const char *format, ...);

int main() {
  int x = 0;
  if (scanf("%d", &x) == 1) return x + 1;
  return 0;
}
