// A malloc of symbolic size: the next allocation starts after the whole block, however large
// it is. With fixed strides a block of more than 65536 units (cells, or bytes under the bytes
// model) overlapped the next allocation.
extern void abort(void);
void reach_error() { abort(); }
extern int __VERIFIER_nondet_int(void);
void *malloc(unsigned long);

int main(void) {
  int n = __VERIFIER_nondet_int();
  if (n <= 0 || n > 1000000) return 0;
  int *p = malloc(n * sizeof(int));
  int *q = malloc(sizeof(int));
  if (!p || !q) return 0;
  *q = 5;
  p[n - 1] = 7;
  if (*q != 5) reach_error();
  return 0;
}
