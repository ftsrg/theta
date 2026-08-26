// Preprocessed sources -- the LDV `.i` files above all -- have had the glibc headers
// stripped, so `memcpy(dst, src, n)` arrives with no declarator at all. The *callee
// identifier* then failed to resolve ("No such variable or macro: memcpy") long before
// MemoryFunctionsPass, which already models the call, ever saw it. ~240 of run 84's
// before-parsing failures were this.
/* no #include at all: memcpy/memset/malloc/free have no declarator, as in LDV .i files */
extern void abort(void);
extern int __VERIFIER_nondet_int(void);
void reach_error(){ abort(); }
typedef unsigned long size_t;
int main() {
  char *p = malloc(4);
  if (!p) return 0;
  memset(p, 0, 4);
  if (p[0] != 0 || p[3] != 0) reach_error();
  char src[4] = {1,2,3,4};
  memcpy(p, src, 4);
  if (p[0] != 1 || p[3] != 4) reach_error();
  free(p);
  return 0;
}
