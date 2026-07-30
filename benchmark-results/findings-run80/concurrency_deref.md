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

### Subgroup B: FINISHED. Exact numbers from all three variants

All three dumps show the same mismatch: the size registered for an array-of-structs object is the
**element count**, while every `arr[i].f` access addresses that object with the **flat cell offset**
`i * unitCount(elem) + fieldOffset`.

**1) Plain GLOBAL array of structs** (`globalarr.c`, `scratchpad/dump_ga/xcfa.dot`):
```
(assign __theta_ptr_size (array (1 3) (default 0)))        # arr object base 1, size 3  <- element count
(write ... (deref 1 0 Int) 2) (deref 1 1) 2) (deref 1 2) 2) # per-element objects, size 2 each
bad_deref: (<= (read __theta_ptr_size 1) 0/1/2)            # zero-init, pass (0,1,2 < 3)
bad_deref: (<= (read __theta_ptr_size 1) 5)                # arr[2].b  -> 3 <= 5 TRUE -> TAUTOLOGY
```
Note both addressings coexist in one program: the nested one `(deref (deref 1 k) f)` for the
element objects and the flattened one `(deref 1 5)` for `arr[2].b`.

**2) GLOBAL struct member array of structs** (safestack_relacy shape, `dump_ss`):
`size[stack.array object] = 3`, accesses at flat offsets 0..5 => `3 <= 5` TRUE.

**3) LOCAL array of structs** (`localarr.c`, `scratchpad/dump_la/xcfa.dot`) — full init edge:
```
(assign __malloc (+ __malloc 3))
(assign call_alloca_ret0 (+ __malloc 1))
(assign __theta_ptr_size (write __theta_ptr_size call_alloca_ret0 3))   # size 3 <- element count
(assign main::arr (+ call_alloca_ret0))
...
bad_deref: (<= (read __theta_ptr_size main::arr) 5)                     # 3 <= 5 TRUE -> TAUTOLOGY
(memassign (deref main::arr 5 Int) 1)                                  # the real store, cell 5
```
(My earlier guess that the local case was an *unconstrained base* is RETRACTED — the base and size
are both assigned; the size is just in the wrong unit. `AllocaFunctionPass` had already lowered the
`alloca` marker, which is why my first grep for `alloca` found nothing.)

TRUE SCOPE of subgroup B: **every array whose elements occupy more than one flat cell**, i.e. any
array of (non-union) structs — global, struct-member, or local. Not member-specific, not
global-specific. Any access at flat offset >= elementCount false-alarms, so it bites from
`arr[1].<second field>` onward: it is not an edge case, it is the common case for any such array
touched beyond its first element.

Open sub-question (does not change the fix): `allocateStackArray` (FrontendXcfaBuilder.kt:431-436)
*claims* to use `flatArraySize(type)` (= `size * elementType.unitCount` = 6 here), yet the local
model registers 3. Either the local declaration reaches a third path, or `flatArraySize`'s
`is CStruct ->` branch does not fire because `type.embeddedType` is not a `CStruct` at that point.
Discriminator running: a local `int arr[3][2]` — if it registers 6 the array-of-array branch works
and the CStruct branch is the broken one; if 3, the declaration bypasses `flatArraySize` entirely.

### Subgroup B SCOPE ESCALATION (verified): it hits plain multi-dimensional arrays too

`ga2d.c` / `la2d.c` — **no structs at all**:
```c
int arr[3][2];                                            /* or local to main */
int main(void) { arr[2][1] = 1; return arr[2][1]; }
```
Both **Unsafe** (`false(valid-deref)`) under the default multi model, PRED_CART. Expected Safe.

GLOBAL 2-D dump (`dump_ga2/xcfa.dot`) — identical shape to the array-of-structs case:
```
(assign __theta_ptr_size (array (1 3) (default 0)))      # arr object base 1, size 3  <- ROW count
(write ... (deref 1 k Int) 2)  k=0,1,2                   # each ROW gets its own 2-cell object
bad_deref: (<= (read __theta_ptr_size 1) 0/1/2)          # zero-init via the NESTED view: passes
bad_deref: (<= (read __theta_ptr_size 1) 5)              # arr[2][1] via the FLAT view: 3<=5 TAUTOLOGY
```
LOCAL 2-D dump (`dump_la2/xcfa.dot`) — full init edge:
```
(assign __malloc (+ __malloc 3)) ; (assign call_alloca_ret0 (+ __malloc 1))
(assign __theta_ptr_size (write __theta_ptr_size call_alloca_ret0 3))   # size 3 <- ROW count
(assign main::arr (+ call_alloca_ret0))
bad_deref: (<= (read __theta_ptr_size main::arr) 5)                     # 3 <= 5 TAUTOLOGY
(memassign (deref main::arr 5 Int) 1)                                   # real store at flat cell 5
```

FINAL SCOPE of subgroup B: **any array whose element occupies more than one flat cell** — an array
of non-union structs, or a multi-dimensional array — in *any* storage class (global, struct member,
local). The object's size is registered as its **outer element count** while accesses use the
**flattened** offset `outerIndex * innerCells + innerOffset`. Every access with flat offset >=
outer count is a tautological `__THETA_bad_deref`. `int a[3][2]` is a 2-line reproducer.

Two views of the same object genuinely coexist in the emitted model — the nested one (each row /
element gets its own base id stored in the parent's cell, correctly sized) is used by the
zero-initialisation, and the flattened one is used by ordinary indexing. They disagree, and the size
map only ever describes the nested one.

WHICH SITE: for the GLOBAL path it is `FrontendXcfaBuilder.kt:752-755`, which sizes the object with
`getArraySize(type, initExpr)` (outer element count) instead of `flatArraySize(type)`.
For the LOCAL path `allocateStackArray` (`FrontendXcfaBuilder.kt:431-436`) *claims* to use
`flatArraySize(type)` (which would give 6), yet the model registers 3 — so either a third path emits
that `alloca`, or `flatArraySize` falls through its `else -> size` branch because
`type.embeddedType` is not the `CArray`/`CStruct` it expects. **COULD NOT DETERMINE which**, because
distinguishing them needs a log/assert inside the frontend and I am not permitted to rebuild.

### NOTE: the prebuilt dist WAS rebuilt at 07:53 today and already contains the subgroup-A fix

`theta.jar` mtime = Jul 30 07:53 (my first dumps were 21:46 the previous evening). Proof the fix is
in: `bounded_mpmc_check_full` dumped now shows `(assign __sp 327680)` = 5 * FLAT_STRIDE and
`(assign __sp (+ __sp 196608))` = +3 * FLAT_STRIDE, whereas yesterday's ticketlock dump showed
`(assign __sp 5)` / `+3`. So `__sp` is now on the flat address line.
=> contrary to the coordinator's note, subgroup A can be re-verified by running, not only reasoned
about. Doing that below.

Also learned from that dump: for `--property no-data-race`, `MemsafetyPass.enabled` is false, so
`__theta_ptr_size` and all the deref checks are absent from the model entirely. **The size map
therefore cannot be the mechanism behind `bounded_mpmc_check_full`'s false `false(no-data-race)`.**
The only flat-specific mechanism left for that verdict is *address aliasing* — two distinct objects
folded onto the same flat address — which is exactly what the `__sp` scaling fixes. So that verdict
is now plausibly fixed too, and is worth re-running rather than reasoning about.

### VERIFIED: the subgroup-A fix in the rebuilt dist fixes all three subgroup-A repros

`--memory-model flat --backend CEGAR --domain EXPL --property valid-memsafety --architecture ILP32`:
| file | before (jar of 21:46) | after (jar of 07:53) |
|---|---|---|
| `inline.c`  `int *p = &s.b; return *p;` | Unsafe (false alarm) | **Safe** |
| `arr.c`     `rd(&a[2])` on `int a[4]`   | Unsafe (false alarm) | **Safe** |
| `midfield.c` `rd(&s.b)` via a callee     | Unsafe (false alarm) | **Safe** |

### VERIFIED at model level: the tautology is gone from the real ticketlock task too

Post-fix ticketlock dump (`scratchpad/dump_tl2/xcfa.dot`), the edge that used to be a tautology:
```
before: (<= (read __theta_ptr_size 131073) 0)                        # 0 <= 0  -> ALWAYS TRUE
after : (<= (read __theta_ptr_size (* (div 131073 65536) 65536))     # size[131072] = 2
              (+ (mod 131073 65536) 0))                             # offset    = 1
                                                                    # 2 <= 1   -> FALSE. correct.
```
All seven distinct bad-deref guards in the procedure now go through
`(* (div addr 65536) 65536)` / `(mod addr 65536)`, including the ones whose address is a parameter
(`vatomic32_read::a`) or loaded from memory (`(deref 0 (+ 131072 1))`). The subgroup-A defect is
repaired in the model.

MINOR PERF NOTE on the fix (not a correctness issue): the `div`/`mod` are **not constant-folded**
even when the address is a literal — the model literally carries `(div 131072 65536)`. Every deref
check now hands the solver two extra arithmetic ops (four counting the negated copy on the twin
edge). Since the guard sits on every dereference edge, tasks that currently finish close to the
limit may tip over. Folding `div`/`mod` of two literals in `SimplifyExprsPass` would remove most of
the cost for statically-based objects, which is the common case.

### CONFIRMED: subgroup B is untouched by the subgroup-A fix

`globalarr.c` (`struct Item arr[3]` global, `arr[2].b = 1`) against the 07:53 jar, default multi
model, PRED_CART: still `(Property valid-deref) (SafetyResult Unsafe)`. Expected. The two bugs are
independent — subgroup A lives in the flat *checking* formula, subgroup B in the *frontend's* choice
of unit for an array object's size, under the default multi model.

---

## SUGGESTED FIX — subgroup B

FILE: `subprojects/xcfa/c2xcfa/src/main/java/hu/bme/mit/theta/c2xcfa/FrontendXcfaBuilder.kt`

1. **Global array path, lines ~752-755.** Sizes the object with
   `getArraySize(type, initExpr)` (outer element count). It must be the flat cell count, i.e. the
   same `flatArraySize(type)` the stack path names — with a fall-back to the element count when
   `flatArraySize` returns null (non-fixed dimensions).
2. **The local/stack path.** `allocateStackArray` (lines 431-436) already calls
   `flatArraySize(type)`, which for `int[3][2]` and for `struct Item[3]` should be 6 — yet the
   emitted model registers 3. So either this is not the site that fires for a plain local array
   declaration, or `flatArraySize` is falling through its `else -> size` branch because
   `type.embeddedType` is not the `CArray`/`CStruct` it expects. One `logger`/assert inside
   `flatArraySize` settles it; I could not, since rebuilding is out of scope for me.
3. **`giveStructObjectStorage`, lines ~329-345.** Sizes a struct as `type.unitCount` (one unit per
   field) and recurses only into `CStruct` fields, never `CArray` fields. The member-array object's
   size therefore comes from elsewhere and is again the element count (safestack: 3 for a 6-cell
   object). Whatever sizes a member array must use the flat cell count too.

RISK: **low, and it cannot hide a real invalid dereference.** The change only ever makes an object
*larger* in the size map, so it converts "reported invalid" into "accepted" — but only for flat
offsets in `[elemCount, elemCount*innerCells)`, and those cells genuinely belong to the object under
the flattened layout that every ordinary access uses. Today's reports there are spurious, not real
detections. Genuine out-of-bounds (offset >= flat cell count) is still caught unchanged.
RISK to race detection: **none.** `MemsafetyPass.enabled` is false for `--property no-data-race`
(verified: the bounded_mpmc no-data-race dump contains no `__theta_ptr_size` at all), so the size map
plays no part in the race checker.

SIDE OBSERVATION worth its own ticket: for an *uninitialised* aggregate the frontend builds a
**second, nested** representation — each row/element gets its own base id stored in the parent's
cell, correctly sized — and the zero-initialisation writes through *that*, while every ordinary
`arr[i][j]` / `arr[i].f` access uses the flattened cells. The nested storage is written and never
read (dead), but it means the flat cells are not what the zero-initialisation wrote to. Whether the
flat cells still read as 0 depends on the memory backend's default; probe running (`zeroinit.c`,
`if (arr[2].b != 0) reach_error();` on an uninitialised global array of structs — an `Unsafe` there
would be a value-level unsoundness independent of memsafety).

---

## SUMMARY TABLE — final attribution of the 8 tasks I was given

| task | subgroup | cause | status |
|---|---|---|---|
| libvsync/ticketlock | A | flat check indexes size map with a mid-object address | **fixed** in 07:53 jar (model verified) |
| libvsync/mcslock | A | same | fixed (same mechanism; `&nodes[tid]`, `&l->owner`) |
| libvsync/cnalock | A | same | fixed (same mechanism) |
| libvsync/bounded_mpmc_check_full | A | same | fixed (valid-deref side) |
| pthread-complex/elimination_backoff_stack | A | same (`&threads[i]`, `&location[mypid]`, `&p->cell`) | fixed |
| termination-dietlibc/stpcpy | A | same — **not** the multi-model str* bug, see below | fixed |
| pthread-complex/safestack_relacy | **B** | array-of-structs object sized in elements, addressed in flat cells | **OPEN** |
| termination-recursive-malloc/rec_strcopy_malloc | neither | runs under multi, no flat fallback — the parallel str*/loop-incremented-pointer-parameter investigation | not mine |

`bounded_mpmc_check_full` also has a wrong `false(no-data-race)`; it is produced under the same flat
fallback, and since `MemsafetyPass` is off for that property the only flat-specific mechanism is
address aliasing from unscaled `__sp` — which the 07:53 jar fixes. Not re-run (needs the full
concurrent check to terminate); flagged as likely-fixed-but-unverified.

## CONFIDENCE

* Subgroup A root cause: **high**. Tautological guard read straight off the model dump, 4- and
  5-line repros, offset-0 control that stays Safe, correct behaviour under multi, and the fix
  (already landed) flips all three repros to Safe and removes the tautology from the real task.
* Subgroup B root cause: **high**. Exact size values and exact access offsets read off three
  independent dumps (plain global array, struct-member array, local array), a 3-line repro, and a
  control (`int arr[3]` inside a struct) that is Safe precisely because element count == cell count.
* Subgroup B *scope* (multi-dimensional arrays as well as arrays of structs, all storage classes):
  **high** — verified by running, not inferred.
* Which source line mints the wrong size on the **local** path: **low** — see "could not determine".
* `bounded_mpmc_check_full`'s false `false(no-data-race)` mechanism: **low/medium**. I ruled out the
  size map (it does not exist for that property) and identified unscaled-`__sp` address aliasing as
  the only remaining flat-specific mechanism, but never exhibited an actual aliased pair.

## ANYTHING I COULD NOT DETERMINE

1. **Which frontend site registers the wrong size for a LOCAL array** whose elements span several
   cells. `allocateStackArray` names `flatArraySize` (would be 6) but the model shows 3. Either a
   third path emits that `alloca`, or `flatArraySize` falls through `else -> size`. Distinguishing
   needs a print inside the frontend; rebuilding was out of scope for me.
2. **Whether `bounded_mpmc_check_full`'s false `false(no-data-race)` is really the `__sp` overlap.**
   I proved the size map is irrelevant there and that `__sp` is now scaled, but I did not exhibit two
   objects that actually collided pre-fix, and I did not re-run the (long, concurrent) task post-fix.
3. **Whether the five subgroup-A concurrency tasks now come out `true` rather than `unknown`.** The
   false alarm is gone at model level, but these are concurrent lock algorithms and the checker still
   has to *prove* safety; a timeout is a plausible outcome. The real ticketlock run I launched was
   still going when I finished. This needs the benchmark, not a single local run.
4. **Whether the flat cells of an uninitialised aggregate read as 0.** Probe (`zeroinit.c`) launched
   but not returned. If it is Unsafe, there is a value-level unsoundness (zero-init writes the dead
   nested storage, not the flat cells that accesses use) that is independent of memsafety.

---

## RESIDUAL RISK REVIEW of the (already landed) subgroup-A fix

1. **Could it hide a real invalid dereference? Yes, in one narrow class — flag it.** Recovering the
   base as `(addr / STRIDE) * STRIDE` means an access more than `FLAT_STRIDE` (65536) cells past its
   object's base is attributed to a *different* object's slice, and is accepted if that object is
   large enough. Before the fix such an access was reported (accidentally, because `size[base+huge]`
   was 0). This is the limitation `FlatMemoryPass`'s own doc already acknowledges ("as long as no
   object is larger than FLAT_STRIDE cells"); the fix turns an accidental catch into a possible miss.
   Out-of-bounds in sv-benchmarks is by a few cells, so the practical exposure is small, but it is a
   real narrowing of detection and should be recorded.
2. **Does the scaled `__sp` risk hiding real races? No — it removes a source of spurious ones.**
   `AtomicAccessUtils.addressesAtomicData` (lines 58-69) already decodes a flat address as
   `isAtomicObjectCell(addr / STRIDE, addr % STRIDE)`. With the *old* unscaled `__sp`, an
   address-taken local's base (5, 8, 11, …) divided by 65536 gave id **0**, which is never a recorded
   object, so the lookup always answered "not atomic" — keeping the access in the race check
   (over-reporting, per that function's own comment). With `__sp` scaled the division now yields the
   real id, matching what `recordReferencedObjectAtomicity` records against the raw `cnt`. So the
   scaling makes the atomicity resolution *correct* where it was previously always-miss. Direction of
   change: fewer spurious races, no new missed ones.
3. **Cost.** See the perf note above: `div`/`mod` are not constant-folded, so every deref guard grew.

## `bounded_mpmc_check_full`'s false `false(no-data-race)` — TWO candidates, NEITHER verified

For that property `MemsafetyPass` is off, so the size map is out (verified from the dump). Remaining
flat-specific candidates:
* (a) **Address aliasing from the old unscaled `__sp`**: local objects sat at 5/8/11/… inside the
  first stride slice, only 3 apart, while `allocateReferenced` can hand one a size > 3 — two distinct
  local objects then overlap on the flat address line. Fixed by the scaling.
* (b) **Atomicity lookup always missing for address-taken locals** (point 2 above): pre-fix every
  such object resolved to id 0, so `_Atomic` cells were treated as ordinary and became race
  candidates. Also fixed by the scaling. Weakened as an explanation by the fact that the `__atomic_*`
  builtins are additionally lowered into `F[ATOMIC_BEGIN]`/`F[ATOMIC_END]` blocks (visible in the
  ticketlock dump), which the race checker should already respect.
I did not exhibit a concrete aliased pair or a concrete mis-resolved atomic cell for either, and I
did not re-run the task post-fix (it is a long concurrent check). **Both remain hypotheses**; note
they are both fixed by the same landed change, so a re-run of that one task settles it.

---

## RUNS THAT DID NOT RETURN (machine contention, not results)

The box was shared with another agent running an unserialised `--portfolio STABLE` job, so my
`flock`-queued runs starved. These are INCONCLUSIVE, not negative:
* real `ticketlock.i` post-fix with the benchmark's winning config
  (`--domain PRED_CART --refinement BW_BIN_ITP --initprec ALLASSUMES --por AASPOR --coi COI
  --memory-model flat`) — never returned a verdict. The model-level check above already shows the
  tautology is gone; whether the checker now *proves* Safe or times out is unknown.
* `zeroinit.c` (does an uninitialised global array of structs read as 0 through the flat cells?) —
  killed by its own timeout while queued. Still worth answering: an `Unsafe` there would be a
  value-level unsoundness independent of memsafety.
* post-fix audits of `mcslock.i` / `elimination_backoff_stack.i` dumps (checking no bad-deref guard
  bypasses the new div/mod recovery) — queued, never ran.

---
# ROUND 2 (against commit 145bffaac0, dist rebuilt 13:24)

## MAJOR: subgroup B hits most of the family too — the A fix alone will NOT clear them

The post-fix `elimination_backoff_stack` dump (`scratchpad/dump_ebs2`, taken on the 07:53 jar)
audits clean for subgroup A — **all 77 distinct bad-deref guards go through the new div/mod
recovery, none bypasses it**. But its size registrations expose subgroup B in the wild:
```
(array (131072 1) (65536 1) (262144 8) (458752 4) (default 0))
write __theta_ptr_size 3014656 4      # int allocated[4]      -> 4  (correct, 1 cell/elem)
write __theta_ptr_size (deref 0 (+ 458752 k) Int) 3)  k=1,2,3  # per-element objects, 3 units each
```
* `262144` (=4·STRIDE) size 8 = `ThreadInfo *location[8]` — correct, pointers are 1 cell.
* `458752` (=7·STRIDE) size **4** = `ThreadInfo threads[4]`. But
  `struct ThreadInfo { unsigned id; int op; Cell cell; }` is **3 units** (the size-3 writes above
  confirm it), so the object spans 4·3 = **12** flat cells and was registered as 4.
  `threads[i].op` is at flat offset `i*3+1`, i.e. up to 10 — so every access with `i >= 2`
  false-alarms. Not a tautology (i=0 passes), but guaranteed once i>=2 is reachable, and it is
  (4 threads).

By the same argument from source, **`mcslock` is affected too**:
`struct mcs_node_s { mcs_node_t *next; vatomic32_t locked; }` = 2 units, global
`struct mcs_node_s nodes[NTHREADS=3]` -> registered 3, needs 6; `&nodes[tid]` for tid>=2 lands past
the registered size. `cnalock` / `bounded_mpmc_check_full` have the same array-of-struct shape.

=> **Revised attribution: subgroup B is not just `safestack_relacy`. It very likely covers
`elimination_backoff_stack`, `mcslock`, `cnalock` and `bounded_mpmc_check_full` as well** (verified
from the dump for elimination_backoff_stack; inferred from the struct definitions for the rest,
mcslock dump running). Subgroup B is therefore the blocking item for this whole family, not a
one-task footnote.

## ITEM 1 — RESOLVED: the local-path site is in the C frontend, not FrontendXcfaBuilder

`allocateStackArray` is **never called for a declared local array**, which is why its correct
`flatArraySize` never applies. Two independent confirmations in the source:

* `FrontendXcfaBuilder.kt:255-258` — local variables get stack storage only when
  `type is CStruct`:
  ```kotlin
  val type = CComplexType.getType(flatVariable.ref, parseContext)
  if ((type is CStruct) && builder.getParams().none { it.first == flatVariable }) {
    allocateStackStruct(flatVariable.ref, type, initStmtList)
  }
  ```
  A local `CArray` is not handled here at all.
* the doc comment on `allocateArrayElements` (`FrontendXcfaBuilder.kt:451-453`) says it outright:
  *"Split out from [allocateStackArray] because a **declared local array already gets its own base
  from the `alloca` the frontend emits at the declaration**; only its subobjects are missing."*

**THE SITE:** `subprojects/frontends/c-frontend/src/main/java/hu/bme/mit/theta/frontend/transformation/grammar/function/FunctionVisitor.java`, `visitBodyDeclaration`, line **968**:
```java
if (declaration.getActualType() instanceof CArray cArray) {
    ...
    final var alloca = new CCall("alloca", List.of(cArray.getArrayDimension()), parseContext);
```
It passes **`cArray.getArrayDimension()` — the OUTER dimension only** — as the alloca size, which
`AllocaFunctionPass` then writes straight into `__theta_ptr_size`. That is exactly the 3 observed for
both `struct Item arr[3]` and `int arr[3][2]`.

So `flatArraySize` was a red herring: it is only reached for arrays nested *inside* a struct field
(via `allocateStackSubobject` -> `allocateStackArray`), never for a top-level local declaration.

### The three sites that must all change, and how

| storage class | site | currently passes | must pass |
|---|---|---|---|
| local declaration | `FunctionVisitor.java:968` | `cArray.getArrayDimension()` (outer dim) | `dimension * flatCellsPerElement` |
| global | `FrontendXcfaBuilder.kt:752-755` | `getArraySize(type, initExpr)` (outer count) | `flatArraySize(type) ?: getArraySize(...)` |
| struct member array | whatever sizes it (safestack registered 3 for a 6-cell object) | outer count | flat cell count |

`flatCellsPerElement` is computable entirely inside the C frontend, so the local fix needs no new
module dependency: `CArray.getEmbeddedType()` (line 47) and `CStruct.getUnitCount()` (line 155) are
both public. Recursively: `CStruct` (non-union) -> `getUnitCount()`; `CArray` -> `dim * cells(embedded)`;
anything else -> 1. Note `getArrayDimension()` returns a `CStatement` (VLAs are supported), so the
multiplication must be built as an expression `dim * constantCells`, not folded into an int.

**Internal contradiction worth citing in the commit:** `allocateArrayElements` already allocates an
element's nested aggregate at flat offset `index * cells + unitOffsetOf(field)`
(`FrontendXcfaBuilder.kt:466-474`) — i.e. the *subobject* bookkeeping already assumes the flattened
layout — while the array's own registered size uses the element count. The two halves of the same
declaration disagree.

RISK of the subgroup-B fix: unchanged from my earlier assessment — it only ever makes objects larger
in the size map, over cells that genuinely belong to them under the layout accesses use, so **it
cannot hide a real invalid dereference** (a genuine OOB past the flat cell count is still caught) and
it **cannot hide a race** (`MemsafetyPass` is off for `no-data-race`).

## TESTABLE PREDICTION for item 3 (which of the five the A fix alone clears)

Of the five subgroup-A concurrency tasks, only **`ticketlock` has no array whose elements span more
than one flat cell**: `ticketlock_t lock` is a struct of two `vatomic32_t` (each a 1-field struct,
handled correctly by `giveStructObjectStorage`'s CStruct recursion), and `main`'s `pthread_t t[3]` is
an array of scalars (1 cell each). The other four all carry an array of multi-cell structs:
* `mcslock`  : `struct mcs_node_s nodes[3]`, element = 2 units
* `cnalock`  : same shape
* `bounded_mpmc_check_full` : bounded-queue array of structs
* `elimination_backoff_stack` : `ThreadInfo threads[4]`, element = 3 units (verified in the dump)
plus `safestack_relacy` (multi model): `SafeStackItem array[3]`, element = 2 units.

PREDICTION: post-A-fix, `ticketlock` should no longer be Unsafe, while the other four (and
safestack_relacy) should still be Unsafe on subgroup B. Testing `mcslock` now — an Unsafe there is
fast to find and would confirm the family-wide subgroup-B claim empirically.

## ITEM 2 — REFRAMED: both of my earlier candidates are WRONG; the `__sp` scaling will NOT fix it

Decisive evidence from `libvsync/src/include/vsync/queue/bounded_mpmc.h`:
```c
    q->buf[curr % q->size] = v;        /* line 88, producer */
    *v = q->buf[curr % q->size];       /* line 124, consumer */
```
**The ring-buffer slots are plain `void *`, not `vatomic*`.** Only the four ticket counters
(`phead`/`ptail`/`chead`/`ctail`) are atomic. The buffer accesses are genuinely non-atomic reads and
writes to shared memory; the program is race-free only because the ticket protocol guarantees no two
threads touch the same slot concurrently.

Consequences for my two earlier candidates:
* (a) **address aliasing from unscaled `__sp` — RULED OUT.** The post-fix no-data-race dump
  (`scratchpad/dump_mpmc/xcfa.dot`) shows every base is already a clean multiple of the stride
  (`65536`, `131072`, `524288`, `2031616` = 1/2/8/31 x STRIDE, plus mid-object `131073..131075`).
  Nothing sits in the first slice; no two objects can overlap.
* (b) **atomicity-lookup miss — RULED OUT as the cause.** It is real (`addressesAtomicData` bails
  with `offset.asConstantBigInteger() ?: return false`, so an atomic cell at a *symbolic* index is
  never recognised — and this dump does contain `deref 0 (+ 2031616 writer::for19::idx)`), but it is
  irrelevant here because the slots are **not atomic in the first place**. There is no exemption to
  miss.

WHAT IT ACTUALLY IS (medium confidence, static): the checker found a concrete pair of conflicting
accesses to `buf[curr % q->size]` that it believes concurrent, i.e. it failed to establish the
ticket protocol's mutual exclusion. That is the **CAS/ownership-gated CEGAR precision gap already
recorded for libvsync** (see memory `project_svcomp27_batch64_libvsync`: "mcslock + bounded_mpmc
reproduce real wrong verdicts fast, both = same CAS/ownership-gated CEGAR precision gap as
rec_ticketlock"). It is orthogonal to everything in this investigation, and **the `__sp` scaling
should not be expected to fix it.**

I cannot tell from the model alone whether it is a precision gap (should have been `unknown`) or an
unsound modelling of the atomic RMW that lets two threads take the same ticket. Distinguishing them
needs the counterexample interleaving from the witness for that specific run, which I could not get:
see the starvation note below. **Do not count this task as fixed by 145bffaac0.**

## ITEM 1 — EMPIRICAL PROOF, and the contradiction inside a single init edge

`repro/outerarr.c` (3 lines) — local `struct Outer arr[3]`, `Outer { struct Inner in; int y; }`,
so `unitCount(Outer)` = 2 and the array spans 3x2 = 6 flat cells. Its whole init edge
(`scratchpad/dump_oa/xcfa.dot`):
```
(assign __malloc (+ __malloc 3)) ; (assign call_alloca_ret0 (+ __malloc 1))
(assign __theta_ptr_size (write __theta_ptr_size call_alloca_ret0 3))   # size 3 = OUTER DIMENSION
(assign main::arr (+ call_alloca_ret0))
(write __theta_ptr_size (deref main::arr 0 Int) 1)   # Inner of arr[0], flat offset 0
(write __theta_ptr_size (deref main::arr 2 Int) 1)   # Inner of arr[1], flat offset 2
(write __theta_ptr_size (deref main::arr 4 Int) 1)   # Inner of arr[2], flat offset 4
```
and the guards it generates:
```
(<= (read __theta_ptr_size main::arr) 0)   # pass
(<= (read __theta_ptr_size main::arr) 2)   # pass  (2 < 3)
(<= (read __theta_ptr_size main::arr) 4)   # 3 <= 4  TRUE -> TAUTOLOGY, during initialisation
(<= (read __theta_ptr_size main::arr) 5)   # 3 <= 5  TRUE -> TAUTOLOGY
```
**The same init edge registers the object as 3 cells and then writes subobjects at flat offsets
0, 2 and 4.** `allocateArrayElements` does run for a declared local array (as its own doc comment
says) and it uses the flattened `index * unitCount + offsetof` layout, while the size beside it is
the outer dimension from `FunctionVisitor.java:968`. That is the contradiction, self-contained in a
3-line program, and it fires while the frontend is still initialising — which is why `localarr.c`
had trace length 4.

## ITEM 3 — settled at MODEL level for the five (no CEGAR run needed)

Checked size registrations in the post-fix (13:24 jar) dumps. All guards in every dump go through the
new div/mod recovery — **subgroup A is clean everywhere** (mcslock 22/22, elimination_backoff_stack
77/77, ticketlock all).

| task | multi-cell array? | registered | needed | subgroup B? |
|---|---|---|---|---|
| **ticketlock** (`dump_tl2`) | none — `lock` = 2 x 1-unit structs, `t[3]` scalars | `lock`=2, `t`=3 | 2, 3 | **CLEAN** |
| **mcslock** (`dump_mcs3`) | `struct mcs_node_s nodes[3]`, elem = 2 units | `655360`->**3** | 6 | **STILL WRONG** |
| **elimination_backoff_stack** (`dump_ebs2`) | `ThreadInfo threads[4]`, elem = 3 units | `458752`->**4** | 12 | **STILL WRONG** |
| safestack_relacy (`dump_ss`, multi) | `SafeStackItem array[3]`, elem = 2 units | `stack.array`->**3** | 6 | **STILL WRONG** |
| cnalock / bounded_mpmc | same array-of-struct shape (from source) | — | — | expected wrong (dump not taken) |

`mcslock`: `&nodes[2]` is flat offset 2x2 = 4, guard `size[655360]=3 <= 4` -> TRUE. Confirmed from the
model, so **the prediction holds: of the five, only `ticketlock` is cleared by 145bffaac0.** The other
four stay wrong until subgroup B is fixed. I did not need the CEGAR runs for this — the tautology is
visible in the size map.

## ITEM 4 — ANSWERED, and it is a WRONG-VERDICT bug outside memsafety entirely

`repro/zeroinit.c`, default multi model, `--property unreach-call`, PRED_CART:
```c
extern void abort(void);
void reach_error() { abort(); }
struct Item { int a; int b; };
struct Item arr[3];
int main(void) { if (arr[2].b != 0) { reach_error(); } return 0; }
```
=> `(Property unreach-call) (SafetyResult Unsafe Trace length: 3)`. **Expected `true`** — a global
array is zero-initialised by C.

So the flat cells of an uninitialised global aggregate do **not** read as 0. The zero-initialisation
writes the *nested* per-element storage (each element gets its own base id and its cells are zeroed),
while `arr[2].b` reads flat cell 5 of the array object, which nothing ever wrote. This is a **false
`false(unreach-call)` on a trivially safe program** — the same nested-vs-flat split as subgroup B, but
now producing wrong answers in the *largest* SV-COMP category rather than only in memsafety.
It is also worse than subgroup B in kind: subgroup B makes a safe program look unsafe via a bogus
*check*; this makes a safe program look unsafe via a bogus *value*.

Note this also means flat cell 0 of such an array holds **element 0's base id** (a pointer value like
65536) rather than data, so reading `arr[0].a` should return a base id. Controls running to confirm
and to bound the scope:
* `zi_scalar.c`  `int arr[3]; if (arr[2] != 0)` — expect **Safe** (1 cell/elem, no nested split)
* `zi_first.c`   `if (arr[0].a != 0)` — expect **Unsafe**, reading a base id as data
* `zi_plainstruct.c` `struct Item s; if (s.b != 0)` — a plain struct, no array

### ITEM 4 — mechanism PROVEN from the model (no further runs needed)

`scratchpad/dump_ga/xcfa.dot` (global `struct Item arr[3]`, array object base 1), every memassign:
```
(memassign (deref 1 0 Int) 4)              # flat cell 0 := element 0's BASE ID
(memassign (deref 1 1 Int) 7)              # flat cell 1 := element 1's BASE ID
(memassign (deref 1 2 Int) 10)             # flat cell 2 := element 2's BASE ID
(memassign (deref (deref 1 k Int) f Int) 0)  k=0..2, f=0..1   # the ZEROES go into the ELEMENT objects
(memassign (deref 1 5 Int) 1)              # `arr[2].b = 1` -> flat cell 5
```
Flat cells **3, 4, 5 are never written by the initialisation at all**. So:
* `arr[2].b` (flat cell 5) reads the array's default — never zeroed => the `!= 0` branch is
  satisfiable => false `false(unreach-call)`. This is the observed Unsafe.
* `arr[0].a` (flat cell 0) reads **4**, i.e. *element 0's base id interpreted as integer data*. A
  pointer value leaks into a data read. Worse in kind than an uninitialised read.
* a scalar array (`int arr[3]`) has one cell per element, so no nested split exists and the zeroes
  land in the very cells that are read — which is why it is correct, and why this has stayed hidden.

So the nested/flat split is not merely a size-bookkeeping mismatch (subgroup B): for an
**uninitialised** aggregate the *data* is written to one representation and read from the other.
Fixing subgroup B's sizes alone would leave this wrong-value bug in place — they must be fixed
together, by making the initialisation write the flat cells (as `initializeFlatArray` already does for
the *initialised* case, `FrontendXcfaBuilder.kt:758-778`) and dropping the per-element objects for
inline-laid-out elements.

NOTE the asymmetry that makes the fix clear: `FrontendXcfaBuilder.kt:758-778` already routes
*initialised* multi-dimensional / flat-scalar-struct arrays through `initializeFlatArray`, precisely
because "the old per-element path gave every element its own base id, which the inline access never
dereferences". The condition is guarded by `initExpr != null`, so the **uninitialised** case still
takes the per-element path — which is exactly the bug. Extending that same treatment to
`initExpr == null` (zero-fill the flat cells) is the natural fix and it is the same code path.

---
## STARVATION REPORT (explicit, as requested — these are NOT results)

At 14:44-15:00 the shared `theta.lock` had **7 waiters** and was held by another agent's long
`--portfolio STABLE` run (a portfolio holds the lock for its whole multi-config sweep). The following
runs of mine never got a turn and produced **no output at all** — do not read them as timeouts or as
negative results:
* `mcslock.i` valid-memsafety FLAT with the benchmark's winning CEGAR config (superseded anyway — the
  subgroup-B tautology is proven from its model dump).
* valid-memsafety dumps of `cnalock.i` and `bounded_mpmc_check_full.i` (would have completed the
  subgroup-B table; both are inferred from their struct definitions instead).
* the three zero-init controls `zi_scalar.c` / `zi_first.c` / `zi_plainstruct.c`. Their expected
  outcomes are *derived from the on-disk `dump_ga` model* (which shows exactly which cells are
  written), so the mechanism is proven without them; the runs would only have been corroboration.
* `bounded_mpmc_check_full` no-data-race re-run — not attempted, because the static analysis above
  shows the `__sp` scaling cannot be the cause.

Earlier (round 1) the same thing killed the real `ticketlock` CEGAR run: it returned `RC=1` with no
verdict line, i.e. killed by its own `timeout` while queued — again not a result.
