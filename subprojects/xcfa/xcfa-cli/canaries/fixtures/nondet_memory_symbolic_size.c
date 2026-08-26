// `__VERIFIER_nondet_memory(mem, size)` with a size that is not known at build time.
//
// The pass has modelled this call for a while, but only by writing out one havoc-and-store pair per
// cell -- which needs the count. A symbolic one was declined, and a declined call is left in place
// as an InvokeLabel to a procedure that does not exist, so it surfaced as
// "No such method __VERIFIER_nondet_memory" (140 of the 836 intel-tdx runs of run 105) even though
// the pass had seen the call and chosen not to model it. The same cap turned away every large
// region: the cap is 4096 cells, and intel-tdx calls this on whole objects whose `sizeof` is 36,864
// (`tdcs_t`), 61,440 (`tdvps_t`) and 81,920 (`tdx_module_global_t`) -- 163,840 statements for one
// call, written out.
//
// It is now lowered to a loop with the havoc INSIDE the body, so every cell still gets its own
// independent unconstrained value; that is what makes the loop the same model rather than a weaker
// one. This fixture takes the symbolic route because it is the only one that can be checked in a
// canary's time budget: any size large enough to trip the 4096-cell cap also needs 4097 loop
// iterations to observe, which no configuration will do in 90 s. The large-size route reaches the
// same lowering through the same helper.
//
// The bug this catches is a fill that does not happen: `n` is pinned to 1, so byte 0 is the ONLY
// byte written and it must be unconstrained. A loop whose bound is off by one -- or that never
// enters its body -- leaves it holding the zero every global starts with, the error is unreachable,
// and this fixture reports SAFE. The companion fixture pins the other end of the region.
//
// One iteration rather than four purely for cost: pinned to 4 this same check is UNSAFE in 117 s,
// which is past a canary's budget; pinned to 1 it is 7 s. The lowering exercised is identical.
extern void abort(void);
void reach_error() { abort(); }
extern unsigned int __VERIFIER_nondet_uint(void);
extern void __VERIFIER_nondet_memory(void *mem, unsigned long size);

unsigned char g_buf[8];

int main() {
  unsigned int n = __VERIFIER_nondet_uint();
  if (n != 1) return 0;
  __VERIFIER_nondet_memory(g_buf, n); /* symbolic byte count */
  if (g_buf[0] == 0xAB) reach_error();
  return 0;
}
