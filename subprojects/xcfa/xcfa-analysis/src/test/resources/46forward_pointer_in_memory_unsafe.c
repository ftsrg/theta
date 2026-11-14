// The written cell is reached through a pointer loaded from memory; the value is unknown.
extern int __VERIFIER_nondet_int(void);
extern void reach_error(void);

int a[2];
int *q;

int main(void) {
  q = &a[1];
  *q = __VERIFIER_nondet_int();
  if (a[1] == 7) reach_error();
  return 0;
}
