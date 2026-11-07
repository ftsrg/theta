// A scanf that assigns nothing (it returns 0 or EOF) leaves its target unchanged.
extern void abort(void);
void reach_error() { abort(); }
extern int scanf(const char *format, ...);

int main() {
  int x = 5;
  int r = scanf("%d", &x);
  if (r < 1 && x != 5) reach_error();
  return 0;
}
