// Two block types from one untyped malloc make the multi build fail, and the bytes retry must
// still bound the _Bool block.
typedef unsigned int size_t;
extern void *malloc(size_t size);
extern void abort(void);
extern int __VERIFIER_nondet_int(void);

void *safe_malloc(size_t size) {
  void *p = malloc(size);
  if (p == 0) abort();
  return p;
}

int *update;
_Bool *done;

int main(void) {
  update = (int *)safe_malloc(sizeof(int) * 2);
  done = (_Bool *)safe_malloc(sizeof(_Bool) * 2);
  int s = __VERIFIER_nondet_int();
  int b = done[s];
  return b;
}
