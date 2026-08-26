// `calloc` was modelled by nothing at all: it reached the analysis as a call to a procedure that
// does not exist and brought the run down with "No such method calloc" (372 runs in the batch-89
// pred_int run, and the second most frequent unmodelled function overall).
//
// It is lowered to malloc + memset. The subtlety is WHERE the fill goes: calloc returns `void *`,
// so at the call itself there is no pointee type and MemoryFunctionsPass cannot tell what a cell
// is -- a memset emitted there gives up and the task merely fails on `memset` instead. The result
// is immediately bound to a properly typed pointer, and that expression carries the real cType in
// the frontend metadata, so the fill is placed after that binding instead. The binding usually sits
// on a LATER edge than the call, which is why the pass scans the whole procedure rather than the
// call's own label list.
//
// Both directions matter here: that the block reads back as zero (below), and -- in the pass's own
// A/B -- that a program branching on `p[i] == 0` is still found reachable, so the fill is real
// rather than the path being vacuously infeasible.
extern void abort(void);
void reach_error() { abort(); }
extern void *calloc(unsigned long, unsigned long);

int main() {
  int *p = (int *)calloc(4, sizeof(int));
  if (!p) return 0;
  if (p[0] != 0) reach_error();
  if (p[3] != 0) reach_error();
  p[2] = 7; /* and it is still ordinary writable memory */
  if (p[2] != 7) reach_error();
  if (p[1] != 0) reach_error();
  return 0;
}
