// A store through a pointer in an atomic unit has to read the localized global, not the stale one.
extern void reach_error(void);
extern void abort(void);
void __VERIFIER_atomic_CAS(int *v, int e, int u, int *r) {
  if (*v == e) {
    *v = u, *r = 1;
  } else {
    *r = 0;
  }
}
int memory[65];
int next_alloc_idx = 1;
int top = 0;
void __VERIFIER_atomic_index_malloc(int *c) {
  if (next_alloc_idx + 2 - 1 > 65)
    *c = 0;
  else
    *c = next_alloc_idx, next_alloc_idx += 2;
}
void push(int d) {
  int oldTop, newTop, ret;
  __VERIFIER_atomic_index_malloc(&newTop);
  if (newTop == 0) abort();
  memory[newTop + 0] = d;
  while (1) {
    oldTop = top;
    memory[newTop + 1] = oldTop;
    __VERIFIER_atomic_CAS(&top, oldTop, newTop, &ret);
    if (ret) return;
  }
}
int main(void) {
  push(10);
  if (top == 0) reach_error();
  return 0;
}
