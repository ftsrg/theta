// Assignment through a dereferenced cast: `*(T *)p = v`. The compound-literal grammar rule
// `( type ) initializer` accepted a *bare* initializer, so on an assignment LHS it swallowed
// `p = v` as the initializer -- `*(int*)q = 1` parsed its `*` operand to null and NPE'd. A compound
// literal is braced (`(T){...}`), so the unbraced form must read as a cast; this builds iff it does.
int x;

int main(void) {
  int *q = &x;
  *(int *)q = 1;
  *(int *)&x = 2;
  return x;
}
