// A declaration's storage class is not part of its type: `typeof(s)` of a `static int s` declares
// an ordinary local, which used to come out static and keep its value across calls.
extern void abort(void);
void reach_error(){ abort(); }

static int s;

int f(void) {
  __typeof__(s) t = 0;
  t++;
  return t;
}

int main(void) {
  f();
  if (f() != 1) reach_error();
  return 0;
}
