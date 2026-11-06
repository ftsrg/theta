// scanf returns EOF or the number of conversions it assigned.
extern void abort(void);
void reach_error() { abort(); }
extern int scanf(const char *format, ...);

int main() {
  int a, b;
  int r = scanf("%d %d", &a, &b);
  if (r < -1 || r > 2) reach_error();
  return 0;
}
