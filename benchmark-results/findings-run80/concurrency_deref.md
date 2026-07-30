# Concurrency `false(valid-deref)` false alarms — investigation log

STATUS: in progress (written incrementally)

## FAMILY / SIZE (confirmed from run 80 XMLs)

Extracted from `benchmark-results/results-2026-07-28_22-15-run80-benchcloud900/*valid-memsafety*.xml.bz2`,
category=wrong, status starts with `false`. Unique concurrency members:

| task | expected | got | memory model actually used | winning (wrong) config |
|---|---|---|---|---|
| c/libvsync/mcslock | true | false(valid-deref) | **flat** (fallback) | MULTITHREAD_PRED_BW_BIN_ITP_ALLASSUMES |
| c/libvsync/ticketlock | true | false(valid-deref) | **flat** (fallback) | MULTITHREAD_PRED_BW_BIN_ITP_ALLASSUMES |
| c/libvsync/cnalock | true | false(valid-deref) | **flat** (fallback) | MULTITHREAD_PRED_COI_SEQ_ITP_ALLASSUMES |
| c/libvsync/bounded_mpmc_check_full | true | false(valid-deref) | **flat** (fallback) | MULTITHREAD_PRED_BW_BIN_ITP_ALLASSUMES |
| c/pthread-complex/elimination_backoff_stack | true | false(valid-deref) | **flat** (fallback) | MULTITHREAD_PRED_BW_BIN_ITP_ALLASSUMES |
| c/pthread-complex/safestack_relacy | true | false(valid-deref) | multi (default) | MULTITHREAD_PRED_BW_BIN_ITP_ALLASSUMES |

Non-concurrent members named in the brief:
| c/termination-dietlibc/stpcpy | true | false(valid-deref) | **flat** (fallback) | KIND-Z3:new |
| c/termination-recursive-malloc/rec_strcopy_malloc | true | false(valid-deref) | multi (default) | PRED_CART-BW_BIN_ITP-Z3 |

Evidence for the "memory model actually used" column: each log begins with
`note: frontend build failed due to a pointer-splitting limitation under --memory-model multi;
retrying with --memory-model flat` for exactly the five concurrency tasks + stpcpy, and
every config line in those logs then carries `memoryModel=flat`. `safestack_relacy` and
`rec_strcopy_malloc` logs carry `memoryModel=null` (= default multi) and no such note.
Logs: `/tmp/.../scratchpad/logs/SV-COMP27_valid-memsafety.<task>.yml.log`

=> **the family splits by memory model, not by lock-vs-string.**

## SUBGROUP A (5 of 6 concurrency tasks + stpcpy): flat memory model, mid-object base in the deref check

ROOT CAUSE (high confidence, see evidence below):
`MemsafetyPass.annotateDeref` assumes `deref.array` is always an object *base id* and that
`__theta_ptr_size[deref.array]` holds that object's whole size. Under `--memory-model flat`
that invariant does not hold: `ReferenceElimination.runFlatReferenceElimination` collapses
`&(deref B O)` to the single scalar `B + O`, so a *mid-object address* legitimately appears in
the `array` slot of a later dereference (`Dereference(B+O, 0)`). The size array only has an
entry at `B`, so `__theta_ptr_size[B+O]` reads 0, the disjunct
`Leq(ArrayReadExpr(sizeVar, deref.array), 0)` is TRUE unconditionally, and the edge to
`__THETA_bad_deref` is always enabled => guaranteed false `false(valid-deref)`.

EVIDENCE (ticketlock.i, `--memory-model flat`, XCFA dump `scratchpad/dump_tl/xcfa.dot`):
```
loc1948 -> __THETA_bad_deref [assume (or (and (and) (or (<= 131072 0) (<= (read __theta_ptr_size 131072) 0) (< 0 0))))]
loc1951 -> __THETA_bad_deref [assume (or (and (and) (or (<= 131073 0) (<= (read __theta_ptr_size 131073) 0) (< 0 0))))]
```
131072 = 2 * FLAT_STRIDE(65536) = the flat base of the first address-taken object (`lock`,
base id 2). **131073 = that base + 1** — the address of the struct's second field, produced by
the flat `&(deref B O) -> B+O` folding and then constant-folded by SimplifyExprs.
`__theta_ptr_size` is only ever written at index 131072 (the `allocateReferenced` call in
ReferenceElimination), so `read __theta_ptr_size 131073` = 0 and the assume is a tautology.

### Airtight evidence chain (ticketlock, flat)

From `scratchpad/dump_tl/xcfa.dot` (procedure `run`):
```
__loc_113134615381733 -> vatomic32_read_init...  [label="(assign vatomic32_read::a 131073)"]
loc1951 -> __THETA_bad_deref [label="(assume (or (and (and) (or (<= 131073 0)
                                    (<= (read __theta_ptr_size 131073) 0) (< 0 0)))))"]
loc1948 -> __THETA_bad_deref [label="(assume (or (and (and) (or (<= 131072 0)
                                    (<= (read __theta_ptr_size 131072) 0) (< 0 0)))))"]
loc1948 -> loc1949 [label="(assume (not ...)) (assign call___atomic_fetch_add_ret9 (deref 0 (+ 131072 0) Int))"]
```
and the only writes to the size array anywhere in the XCFA:
```
main_init: (assign __theta_ptr_size (array (131072 2) (default 0)))   <- lock's whole size = 2 cells at index 131072
(write __theta_ptr_size 262144 3)                                     <- main::t[3]
(write __theta_ptr_size vatomic32_cmpxchg::exp* 1)
(write __theta_ptr_size (deref 0 (+ 131072 0) Int) 1) / (+ 131072 1)
```
`131073` (= `&lock.owner`, i.e. `lock* + 1`) is **never** given a size, so
`(read __theta_ptr_size 131073)` is 0 and `(<= 0 0)` makes the `loc1951 -> __THETA_bad_deref`
assume a **tautology**. Field 0 of the same struct (`131072`) passes, field 1 fails.
`ticketlock_release`/`ticketlock_acquire` both touch `&l->owner`, so the false alarm is
reachable in a straight line by a *single* thread — no interleaving is involved at all.

Mechanism, precisely:
* `ReferenceElimination.runFlatReferenceElimination` (flat path) rewrites `&(deref B O)` to the
  scalar `B + O`. `&lock.owner` therefore becomes the literal `131072 + 1` = `131073`, and that
  value is bound to the pointer parameter and used as the `array` (base) slot of the later
  dereference `(deref a 0)`.
* `MemsafetyPass.annotateDeref` (MemsafetyPass.kt:201-220) builds
  `Or(Leq(deref.array, 0), Leq(sizeVar[deref.array], deref.offset), Lt(deref.offset, 0))`
  — it assumes `deref.array` is an object **base id** and `deref.offset` the in-object index.
  Under flat that invariant is false for every computed/mid-object address.
* Under `multi` the same access becomes `(deref lock* 1)` (base in `array`, 1 in `offset`), so
  `sizeVar[131072]=2 > 1` and the check is correct. **The bug is specific to the flat model.**

CONCLUSION for subgroup A: the concurrency angle is INCIDENTAL. These tasks are wrong only
because the `multi` frontend hits `UnsupportedPointerSplitException` and the CLI silently falls
back to `--memory-model flat`, where the valid-deref instrumentation is simply not flat-aware.

### MINIMAL REPRO for subgroup A (5 lines, sequential, no threads, no heap)

`scratchpad/repro/inline.c`:
```c
struct S { int a; int b; };
struct S s;
int main(void) { int *p = &s.b; return *p; }
```
`--memory-model flat --backend CEGAR --domain EXPL --property valid-memsafety --architecture ILP32`
=> `(Property valid-deref) (SafetyResult Unsafe Trace length: 6)`.  Expected: Safe.

Controls that pin the trigger exactly (same command, only the file changes):
| file | shape | flat verdict |
|---|---|---|
| `field0.c` | `rd(&s.a)` — offset **0** | **Safe** (correct) |
| `midfield.c` | `rd(&s.b)` — offset 1, via a callee | **Unsafe** (wrong) |
| `inline.c` | `&s.b` in main, no call | **Unsafe** (wrong) |
| `arr.c` | `rd(&a[2])` on `int a[4]` | **Unsafe** (wrong) |

=> the trigger is *any* dereference through an address of the form `base + nonzero offset`.
Not the function call, not the loop, not the concurrency, not the heap. Offset 0 works because
`base + 0 == base`, which is exactly the index the size array does hold.

BONUS: `midfield.c` under `--memory-model multi` fails with
`UnsupportedPointerSplitException: bare use of split variable __theta_ref_tmp_0`
— i.e. the same 7-line file also reproduces the *fallback trigger*. Passing a mid-object address
to a function is precisely what the libvsync locks do (`vatomic32_read(&l->owner)`,
`mcslock_acquire(&lock, &nodes[tid])`), which is why this whole family lands in flat.

RULED OUT for subgroup A (with the evidence that killed each):
* "a pointer valid in every real interleaving but not in the model / thread-interleaving bug" —
  killed by `inline.c`: a single-threaded 5-line program reproduces it. Also the failing check
  edge in ticketlock is a *tautology* (`read __theta_ptr_size 131073` is 0 on every path), so no
  schedule is needed to enable it.
* "OC backend / event-graph modelling" — killed by the run-80 logs: OC dies with code 201 on
  these tasks and never produces the verdict; the wrong `false` comes from CEGAR PRED_CART.
* "abstraction imprecision (spurious cex not refuted)" — killed by the fact that the model itself
  admits the trace: the bad-deref assume is unconditionally true, so the cex is genuinely
  feasible *in the model*. Nothing refinement can do.

### Second, independent flat-model defect found while checking the fix (constrains the fix!)

Under flat, object bases are minted **inconsistently**:
* address-taken *globals* → `FlatMemoryPass.flatBaseValue(id)` = `id * 65536`
  (`ReferenceElimination.kt:175`) — correctly scaled. ticketlock: `lock*` init = `131072`.
* frontend/alloca objects → `FlatMemoryPass.flatBaseExpr` = `raw * 65536` — correctly scaled.
  ticketlock: `main::t` = `262144`.
* address-taken *locals* → `__sp`, whose init is `ptrType.getValue("$cnt")` and whose increment is
  `__sp + 3` (`ReferenceElimination.kt:252` and `:269`) — **NOT scaled**. ticketlock JSON:
  `{'name': '__sp', 'initValue': '5'}`, and `vatomic32_cmpxchg::exp*` = 8, 11, ...

Two consequences:
1. Local address-taken objects live at flat addresses 5/8/11/... i.e. all inside the *first*
   stride slice `[0, 65536)`, and only 3 apart while `allocateReferenced` may hand them a size > 3
   (a local struct/array whose address is taken). Two distinct local objects then **overlap** on
   the flat address line — a latent aliasing unsoundness (spurious data races and wrong values).
   `bounded_mpmc_check_full`'s *other* wrong verdict, `false(no-data-race)`, is also produced
   under flat (same fallback note in its no-data-race log) and this is the most likely mechanism —
   NOT verified, see "could not determine".
2. It **blocks the obvious fix**: recovering the base as `(addr / 65536) * 65536` would map every
   `__sp` object to base 0, i.e. NULL, turning today's false alarm into a *different* false alarm.
   Any fix must scale `__sp` too (init `flatBaseValue(cnt)`, increment `3 * FLAT_STRIDE`).

### Extra confirmation of subgroup A on a 4-line file with no struct at all

`scratchpad/repro/arr.c`: `int a[4]; int rd(int*p){return *p;} int main(){return rd(&a[2]);}`
`--memory-model flat` dump (`scratchpad/dump_arr/xcfa.dot`):
```
(assign __theta_ptr_size ... size 4 at index 65536)        # a's base = 1*65536, size 4
loc24..loc27 -> bad_deref: (<= (read __theta_ptr_size 65536) k)   k=0..3   # zero-init, all fine
__loc_623   -> bad_deref: (<= (read __theta_ptr_size 65538) 0)              # &a[2] == 65536+2
__loc_623   -> ...      : (assign rd_ret (deref 0 (+ 65538 0) Int))         # the real access, correct
```
`65538` is never given a size => tautology => `false(valid-deref)`. The access itself is right.

---

## SUBGROUP B (safestack_relacy — the one concurrency member that runs under `multi`)

ROOT CAUSE (high confidence from the model dump; repro pending):
**An aggregate member of a struct gets its own object base id, but that object's size is never
registered in `__theta_ptr_size`.** Accesses through it then compare against size 0.

EVIDENCE (`scratchpad/dump_ss/xcfa.dot`, safestack_relacy, default multi model).
`SafeStack { SafeStackItem array[3]; int head; int count; }`, global `stack`.
Every size registration in the whole XCFA:
```
(assign __theta_ptr_size (array (1 3) (4 3) (default 0)))   # threads[3] -> 3 ; stack -> 3 cells
(write __theta_ptr_size (deref (deref 4 0 Int) 0 Int) 2)    # element object 0 -> 2 cells
(write __theta_ptr_size (deref (deref 4 0 Int) 1 Int) 2)    # element object 1
(write __theta_ptr_size (deref (deref 4 0 Int) 2 Int) 2)    # element object 2
(write __theta_ptr_size Push::head1* 1)
(write __theta_ptr_size Pop::while4::if5::then6::head2* 1)
```
`(deref 4 0)` — the base id of the `stack.array` object itself, stored in `stack`'s cell 0 — gets
**no entry**, so `read __theta_ptr_size (deref 4 0)` = 0.

And the accesses through it are:
```
(assign __theta_ref_tmp_3_base (deref 4 0 Int))                       # &stack.array[2].Next
(assume (or ... (<= (read __theta_ptr_size __theta_ref_tmp_3_base) 5) ...))   -> bad_deref
(memassign (deref __theta_ref_tmp_3_base 5 Int) -1)                   # the real store, cell 5
```
`0 <= 5` is TRUE => tautological `__THETA_bad_deref` edge, exactly as in subgroup A.

A second inconsistency shows up in the same dump and is worth flagging: the *addressing* of
`stack.array[i].Next` uses the **flattened** `i*2 + field` layout (offset 5 for element 2,
field 1 — matching `ReferenceElimination.flatCellCount`, which gives `3 * unitCount(2) = 6`),
while the *allocation* bookkeeping above uses a **nested** layout (three separate 2-cell element
objects reached by base ids at offsets 0..2). The two views disagree; the element-object size
writes are dead bookkeeping for addresses nothing ever forms. Whichever view is intended, the
array object needs a size of 6 (flattened view) for the checks to be right.

NOTE: `MemsafetyPass.allocateReferenced` also under-counts a struct in general:
```kotlin
is CStruct -> if (embeddedType.isUnion) 1 else embeddedType.fields.size
```
vs the `flatCellCount` helper 20 lines above it, which uses `type.unitCount`. For `SafeStack`
these coincide (3). They diverge for bitfield structs. Not the cause here, but the same file
holds two different notions of "how big is a struct".

### Subgroup B: pinned to the exact line, and to an element-count vs flat-cell-count mismatch

Every size-array assignment in the safestack XCFA (`grep 'assign __theta_ptr_size'`):
```
(array (default 0))
(array (1 3) (default 0))                                  # threads[3] -> 3
(array (1 3) (4 3) (default 0))                            # stack -> 3 cells (3 fields)
(write (array (1 3) (4 3) …) (deref 4 0 Int) 3)            # stack.array object -> 3   <-- WRONG, needs 6
(write __theta_ptr_size (deref (deref 4 0 Int) k Int) 2)   # k=0,1,2, dead bookkeeping
(write __theta_ptr_size Push::head1* 1) / Pop::…::head2* 1
```
and `(memassign (deref 4 0 Int) 7)` gives the array object base id 7. So `size[stack.array] = 3`
(the **element count**), while the accesses address it with the **flat cell offset**
`i * unitCount(SafeStackItem=2) + field`, i.e. 0..5:
```
(memassign (deref __theta_ref_tmp_3_base 5 Int) -1)        # &stack.array[2].Next, offset 5
(assume (or … (<= (read __theta_ptr_size __theta_ref_tmp_3_base) 5) …)) -> bad_deref   # 3 <= 5 TRUE
```
=> every access at flat offset >= 3, i.e. `arr[1].b` and beyond, is a tautological bad deref.

The asymmetry is explicit in the source:
* **stack** arrays: `FrontendXcfaBuilder.allocateStackArray` (line 431) uses
  `flatArraySize(type)` — which is `size * elementType.unitCount` for struct elements. CORRECT.
* **global** arrays: `FrontendXcfaBuilder` line ~752-755 uses
  `getArraySize(type, initExpr)` — the plain **element count**. WRONG for struct elements.
* `giveStructObjectStorage` (line ~329) sizes a struct as `type.unitCount` and only recurses into
  `CStruct` fields, never `CArray` fields.

CONFIRMED BY REPRO (`--backend CEGAR --domain PRED_CART`, default multi model, ILP32):
| file | shape | verdict |
|---|---|---|
| `nested2.c` `struct S { struct Item arr[3]; int head; }` global, `s.arr[2].b = 1` | array-of-struct member | **Unsafe** (WRONG) |
| `nested3.c` `struct S { int arr[3]; int head; }` global, `s.arr[2] = 1` | array-of-scalar member | Safe (correct) |

`nested3` is correct precisely because `unitCount(int) == 1`, so element count == flat cell count.

### CORRECTION + escalation: subgroup B is NOT specific to struct members, and NOT global-only

Further repros (`--backend CEGAR --domain PRED_CART`, default multi model, ILP32):
| file | shape | verdict |
|---|---|---|
| `globalarr.c` `struct Item arr[3];` **global**, `arr[2].b = 1` | plain array of structs | **Unsafe** (WRONG) |
| `localarr.c` same array **local to main** | plain array of structs | **Unsafe** (WRONG) |

So my earlier "the stack path (`allocateStackArray` -> `flatArraySize`) is correct" statement is
RETRACTED: the local case is wrong too (and fails even faster, trace length 4 vs 13). The
smallest repro of subgroup B is therefore 3 lines:
```c
struct Item { int a; int b; };
struct Item arr[3];
int main(void) { arr[2].b = 1; return arr[2].b; }
```
Model dumps for both are being taken; the element-count-vs-flat-cell-count mismatch is confirmed
for the global-member case (`size[stack.array]=3` vs offsets 0..5) but the exact numbers for the
plain global and the local case are pending.

### stpcpy is MINE (subgroup A), not the parallel str*/pointer-param-in-loop investigation

`stpcpy.i --memory-model multi --backend NONE` =>
`Frontend failed! UnsupportedPointerSplitException: Unsupported pointer arithmetic: bare use of
split variable stpcpy::dst`.
So stpcpy **cannot be built under multi at all** — the flat fallback is the only model it ever
runs in, and its `false(valid-deref)` is the subgroup-A flat bug. It is not the multi-model
"pointer parameter incremented in a loop in a callee" bug. `rec_strcopy_malloc` does run under
multi and is NOT mine.
