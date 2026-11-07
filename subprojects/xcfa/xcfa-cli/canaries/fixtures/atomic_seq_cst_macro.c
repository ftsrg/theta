// GCC predefines __ATOMIC_SEQ_CST as 5; it has to resolve both as a builtin's order and as a value.
extern void abort(void);
void reach_error() {
  abort();
}
int x;
int main(void) {
  __atomic_store_n(&x, 1, __ATOMIC_SEQ_CST);
  if (__atomic_load_n(&x, __ATOMIC_SEQ_CST) != 1)
    reach_error();
  if (__ATOMIC_SEQ_CST != 5)
    reach_error();
  return 0;
}
