// Static objects used to get bases at fixed strides (three times 65536 units apart: cells, or
// bytes under the bytes model), so an array larger than that ran into the object after it. Each
// object's range is sized by the object itself, so no index into `big` reaches `after`.
extern void abort(void);
void reach_error() { abort(); }
extern int __VERIFIER_nondet_int(void);

int big[200000];
int after;

int main(void) {
  int *pa = &after;
  *pa = 1;
  int i = __VERIFIER_nondet_int();
  if (i < 0 || i >= 200000) return 0;
  big[i] = 2;
  if (*pa != 1) reach_error();
  return 0;
}
