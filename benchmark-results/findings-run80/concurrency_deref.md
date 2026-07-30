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
