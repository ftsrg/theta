// An address-taken *scalar* was never released at the end of its block. It is not an alloca --
// ReferenceElimination gives it a compile-time base at procedure entry -- so it never went through
// registerScoped, no lifetime-end marker was emitted, its __theta_ptr_size entry was never cleared,
// and a dereference after the block was accepted. `memsafety-ext3/scopes1` answered `true` against
// an expected `false`: a use-after-scope missed outright.
//
// The companion fixture scope_lifetime_ok.c covers the must-not-regress direction for allocas; the
// three checks below do it for scalars, where the risk is releasing too early:
//   - `&a` written inside a nested block must end `a`'s life at *a*'s block, not the inner one;
//   - taking an address twice must release once, not twice (that would look like a double free);
//   - statics and globals must never be released at all.
extern void abort(void);
void reach_error(){ abort(); }

static int stat_obj = 5;
int glob = 9;

int main() {
  /* the object outlives a nested block that merely takes its address */
  int a = 7;
  int *pa = 0;
  { pa = &a; }
  if (*pa != 7) reach_error();

  /* two addresses of the same object: one release, not two */
  int b = 1;
  int *p1 = &b;
  int *p2 = &b;
  if (*p1 + *p2 != 2) reach_error();

  /* static and global storage is never scoped */
  int *ps = &stat_obj;
  int *pg = &glob;
  { int *inner = &glob; if (*inner != 9) reach_error(); }
  if (*ps != 5) reach_error();
  if (*pg != 9) reach_error();

  return 0;
}
