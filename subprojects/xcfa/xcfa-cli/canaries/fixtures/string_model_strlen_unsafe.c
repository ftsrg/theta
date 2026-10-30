// The strlen model keeps a reachable error reachable: the length follows the terminator's position.
extern void abort(void);
void reach_error() { abort(); }
extern unsigned long strlen(const char *);
extern int __VERIFIER_nondet_int(void);

int main() {
  int n = __VERIFIER_nondet_int();
  if (n < 0 || n > 3) return 0;
  char a[4] = "xxx";
  a[n] = 0;
  if (strlen(a) == 2) reach_error();
  return 0;
}
