// The other direction, and the one that matters: a program supplying its OWN definition
// must keep it. Routing undeclared names is guarded on `getVar(name) == null`, which is
// precisely what makes this safe where a blanket pre-registration of every function was
// not -- that broke three LDV canaries and converted nothing.
extern void abort(void);
void reach_error(){ abort(); }
typedef unsigned long size_t;
static int calls = 0;
/* the program's OWN memcpy: it counts calls and deliberately copies nothing */
static void *memcpy(void *d, const void *s, size_t n) { (void)s; (void)n; calls++; return d; }
int main() {
  char a[2] = {1, 2};
  char b[2] = {9, 9};
  memcpy(b, a, 2);
  if (calls != 1) reach_error();          /* the definition ran, not the modeled memcpy */
  if (b[0] != 9 || b[1] != 9) reach_error(); /* and it really copied nothing */
  return 0;
}
