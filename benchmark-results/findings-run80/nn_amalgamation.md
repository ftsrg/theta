# Family: neural-network `*-amalgamation` false `false(unreach-call)`

STATUS: root cause established (high confidence). Live document — appended as evidence lands.

## FAMILY

7 tasks named in the assignment, all `unreach-call`, all `expected_verdict: true`,
all `data_model: ILP32` (confirmed from the `.yml` files under
`/home/coder/sv-benchmarks/c/neural-networks/`):

- `softsign_w4_r1_case_1_safe.c-amalgamation`
- `softsign_w4_r2_case_0_safe.c-amalgamation`
- `softsign_w4_r3_case_0_safe.c-amalgamation`
- `softsign_w4_r4_case_0_safe.c-amalgamation`
- `tanh_w4_r1_case_1_safe.c-amalgamation`
- `tanh_w4_r2_case_0_safe.c-amalgamation`
- `tanh_w4_r4_case_0_safe.c-amalgamation`

`filter2_alt` (`c/float-benchs/filter2_alt.c`, unreach-call, expected true) — see
separate section; **does not** share the cause.

## SIZE / SHAPE

~1200 lines of hand-amalgamated `keras2c` runtime + a 30-line `main`. Everything
relevant is in `main` and in `k2c_simpleRNN` / `k2c_simpleRNNcell` /
`k2c_affine_matmul` / `k2c_softsign_func` / `k2c_tanh_func`.

`main` (softsign_w4_r1_case_1_safe):

```c
float input_array[4] = {0.0f}, output_array[4] = {0.0f};
k2c_tensor input_tensor  = {&input_array[0],2,4,{1,4,1,1,1}};
k2c_tensor output_tensor = {&output_array[0],2,4,{1,4,1,1,1}};
input_array[0] = __VERIFIER_nondet_float();
input_array[1] = 1.0f; input_array[2] = 1.0f; input_array[3] = 1.0f;
__VERIFIER_assume(input_array[0] >= -1.0f && input_array[0] <= 1.0f);
hop_softsign_w4_r1(&input_tensor,&output_tensor);
__VERIFIER_assert(isgreaterequal(output_array[2], 0.0f));
```

and the layer body declares, among others:

```c
float simple_rnn_1_fwork[8] = {0};
float simple_rnn_1_state[4] = {0};
float simple_rnn_1_bias_array[4] = {0};
float simple_rnn_1_kernel_array[16] = { /* all 16 values listed */ };
```

The property is in fact input-independent: with `state`, `bias` and `fwork`
correctly zeroed, `h1 = input*I + 0 = [x,1,1,1]`, `h2 = 0*W_rec + h1 = [x,1,1,1]`,
`softsign(1.0) = 0.5`, so `output_array[2] == 0.5 >= 0` regardless of the nondet
input. There is no genuine counterexample.

## ROOT CAUSE

**Local (stack) aggregates with a *partial* brace initializer are not zero-filled.
Only the cells the initializer explicitly names are written; the rest of the object
stays unconstrained.** C11 6.7.9p21 requires the remainder to be initialized as if
it had static storage duration, i.e. to zero.

So `float simple_rnn_1_state[4] = {0};` only writes `state[0]`; `state[1..3]` are
left free, and likewise `bias_array[1..3]`, `fwork[1..7]`, `output_array[1..3]`.
`k2c_simpleRNNcell` then computes `h2 = state·W_rec + (input·K + bias)`, so the
free `state[1..3]` / `bias[2]` let the solver drive `h2[2]` negative,
`softsign(h2[2]) < 0`, `output_array[2] < 0`, assertion violated.

### Evidence 1 — the serialized model shows the missing writes

`--backend NONE --enable-c-serialization` on
`softsign_w4_r1_case_1_safe.c-amalgamation.i`, counting cell-writes per object in
the emitted init code:

```
16 hop_softsign_w4_r1::simple_rnn_1_kernel_array            (16 explicit inits -> correct)
16 hop_softsign_w4_r1::simple_rnn_1_recurrent_kernel_array  (16 explicit inits -> correct)
 9 main::input_tensor*  /  main::output_tensor*  /  ...kernel* / ...recurrent_kernel* / ...bias*
 5 main::input_array          (= {0.0f} -> 1 init write, + 4 later assignments)
 1 main::output_array         (float[4] = {0.0f}   -> ONLY cell 0)
 1 hop_softsign_w4_r1::simple_rnn_1_fwork       (float[8] = {0} -> ONLY cell 0)
 1 hop_softsign_w4_r1::simple_rnn_1_state       (float[4] = {0} -> ONLY cell 0)
 1 hop_softsign_w4_r1::simple_rnn_1_bias_array  (float[4] = {0} -> ONLY cell 0)
```

Arrays whose initializer lists *every* element get every cell. Arrays written
`= {0}` get exactly one cell. That is the bug, visible directly in the model.

### Evidence 2 — 6-line minimal repro, reproduces on all three memory models

```c
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }

int main() {
    float a[4] = {0.0f};
    if (a[2] != 0.0f) { reach_error(); }
    return 0;
}
```

`--backend CEGAR --domain EXPL --architecture ILP32`:

| memory model | result |
|---|---|
| `multi` (default) | `(SafetyResult Unsafe Trace length: 3)` |
| `flat`            | `(SafetyResult Unsafe Trace length: 3)` |
| `bytes`           | `(SafetyResult Unsafe Trace length: 3)` |

So this is **not** a memory-model-specific bug; it is in the C frontend and is
memory-model-independent.

### Evidence 3 — the local/global asymmetry, in both the model and the source

Serialized model for `int a[4] = {1};`:

- as a **global**: `1[0] = 1; 1[1] = 0; 1[2] = 0; 1[3] = 0;` — correct zero-fill.
- as a **local**: `main::a[0] = 1;` — and nothing else.
- `char s[8] = "ab";` as a local: **no init writes at all**.

Matching source asymmetry:

- Correct (global) path:
  `/home/coder/theta/subprojects/xcfa/c2xcfa/src/main/java/hu/bme/mit/theta/c2xcfa/FrontendXcfaBuilder.kt`
  - `initializeFlatArray` (~line 950): `fillFlat` collects `Map<cellIndex, CStatement>`,
    then `for (index in 0 until total) { ... if (value == null) cellType.nullValue ... }`
    — every cell is written, unnamed ones with the type's zero.
  - `initializeCompound` (~line 1080): same shape, `for (i in 0 until dimension)`.
- Buggy (local) path:
  `/home/coder/theta/subprojects/frontends/c-frontend/src/main/java/hu/bme/mit/theta/frontend/transformation/grammar/function/FunctionVisitor.java`
  - `visitBodyDeclaration` (~line 939 struct branch, ~line 1065 array/other branch)
    iterates **only** `initializerList.getStatements()` and calls
    `flattenInitializer` per entry. `flattenInitializer` (~line 905) recurses over
    the entries present. Nothing ever iterates `0 until dimension`, so cells the
    initializer does not name receive no assignment at all.

### Evidence 4 — the real task is Unsafe

`softsign_w4_r1_case_1_safe.c-amalgamation.i`, `--backend CEGAR --domain EXPL
--memory-model flat --architecture ILP32` → `(SafetyResult Unsafe Trace length: 4)`
in 3m45s. (The portfolio reaches `flat` by itself: the frontend prints
`note: frontend build failed due to a pointer-splitting limitation under
--memory-model multi; retrying with --memory-model flat` for this task, because of
the `k2c_activationType*` function pointers.)

## ON THE DIRECTION OF THE UNSOUNDNESS (important)

This is **not** "uninitialized memory is modelled as nondeterministic". That
modelling is correct and must stay. The bug is narrower and the fix direction is
sound:

- A declaration **with an initializer** (`float a[4] = {0};`) is, per C11 6.7.9p21,
  *fully* initialized — the named elements to their values, **all** the rest to
  zero. Theta currently initializes only the named ones. Writing the remainder as
  zero is *required* by the standard, not an assumption.
- A declaration **without** an initializer (`float a[4];`) must keep its current
  nondeterministic modelling. The fix must not touch that branch — in
  `visitBodyDeclaration` it is the `declaration.getInitExpr() == null` else-branch,
  which is a different code path, so the two cannot be confused.

Hence the fix removes behaviours the solver currently has that real C does not, and
adds none. It cannot mask a real bug that depends on reading indeterminate storage,
because in every case it touches the storage is determinate by definition.

## WHAT ELSE IS AFFECTED (same root cause, wider blast radius)

Confirmed `Unsafe` (should be Safe) with `--backend CEGAR --domain EXPL`, all locals:

| repro | code | result |
|---|---|---|
| int array | `int a[4] = {1}; if (a[2] != 0) reach_error();` | Unsafe |
| struct | `struct S {int x,y,z;}; struct S s = {1}; if (s.z != 0) ...` | Unsafe |
| through a pointer | `int a[4]={1}; int*p=&a[0]; if (p[2]!=0) ...` | Unsafe |
| static local | `static int a[4] = {1}; if (a[2] != 0) ...` | Unsafe |
| 2-D | `int a[2][2] = {{1}}; if (a[1][1] != 0) ...` | Unsafe |
| short string literal | `char s[8] = "ab"; if (s[5] != 0) ...` | Unsafe |

Globals are fine (`int a[4] = {1}` / `float a[4] = {0.0f}` as globals do not produce
a wrong verdict; they hit unrelated CEGAR/interpolation failures —
`NotSolvableException` and Z3-legacy `theory not supported by interpolation` — which
are a *separate* issue and not wrong results).

`char s[8] = "ab";` deserves a callout: the local path emits **zero** init
statements, so even `s[0]`/`s[1]` are unconstrained, not just the NUL padding. This
is likely also implicated in the known "alloca-string false-deref" family in
PLAN.md — worth checking there, not confirmed here.

## Evidence 5 — why cartpole/poly pass but softsign/tanh do not

Count of partial aggregate initializers (`[N] = {0}` / `{0.0f}`) per family in
`c/neural-networks/*.i`:

```
  8 linear*      96 poly*      40 softsign*      40 tanh*      0 cartpole*
```

- **cartpole** is `onnx2c`-generated, not `keras2c`: it has **zero** partial
  initializers. Locals are declared bare and then fully assigned. It can never
  trigger the bug. (Ruled out as sharing the cause: nothing to trigger.)
- **poly** *does* have partial initializers, but none of them is a **live**
  uninitialized read:
  - `float input_array[1] = {0.0f}` / `output_array[1] = {0.0f}` / `axesB[1] = {0}`
    — length 1, so the one named cell is the whole object; no missing cells.
  - `dense_68_output_array[1024] = {0}` and `dense_*_fwork[1025|2048] = {0}` — both
    fully overwritten before being read: `k2c_dense` on the `ndim <= 2` path calls
    `k2c_affine_matmul(output->array, …)` which writes every element, and `fwork` is
    only touched on the `ndim > 2` path.
  - poly's real weights *and biases* are fully spelled out:
    `float dense_68_bias_array[1024] = { …1024 values… };`
- **softsign / tanh** use `k2c_simpleRNN`, and there the `= {0}` objects are read
  before they are written:
  - `float simple_rnn_*_state[4] = {0};` — the recurrent state, read by the first
    `k2c_simpleRNNcell` invocation (`h2 = state·W_rec + h1`).
  - `float simple_rnn_*_bias_array[4] = {0};` — a genuinely all-zero bias, read by
    `k2c_affine_matmul`. Unlike poly, it is **not** spelled out, because it is zero.

That is the whole difference: the same frontend bug exists in poly, it just is not
observable there.

## Evidence 6 — the counterexample disappears when the tails are spelled out

`softsign_zerofilled.i` = a scratch copy of
`softsign_w4_r1_case_1_safe.c-amalgamation.i` with only the partial initializers
expanded (`float input_array[4] = {0.0f,0.0f,0.0f,0.0f}`, `fwork[8] = {0.0f × 8}`,
`state[4] = {0.0f × 4}`, `bias_array[4] = {0.0f × 4}`); nothing else changed.

| file | config | result |
|---|---|---|
| original `.i` | CEGAR EXPL, flat, SEQ_ITP | `(SafetyResult Unsafe Trace length: 4)` in 3m45s |
| zero-filled | CEGAR EXPL, flat, SEQ_ITP | no counterexample any more — dies in `Z3ItpSolver.getInterpolant`: `theory not supported by interpolation or bad proof` |

The trace-length-4 counterexample the original finds immediately is gone once the
tails are constrained; the checker then has to do real FP reasoning and hits the
(separate, pre-existing) Z3-legacy FP-interpolation limitation — the same error
`float a[4] = {0.0f}` as a *global* produces. A definitive `Safe` under a
non-interpolating refinement is still in progress (see PENDING).

## All 7 share the cause

Every one of the 7 tasks has exactly the same three offending declarations, four
times over (one per `simple_rnn_*` layer), and the same assertion shape:

```
softsign_w4_r1_case_1_safe   4× bias_array[4]={0}  4× fwork[8]={0}  4× state[4]={0}   assert isgreaterequal(output_array[2],  0.0f)
softsign_w4_r2_case_0_safe   idem                                                     assert isgreaterequal(output_array[4],  0.0f)
softsign_w4_r3_case_0_safe   idem                                                     assert isgreaterequal(output_array[8],  0.0f)
softsign_w4_r4_case_0_safe   idem                                                     assert isgreaterequal(output_array[14], 0.0f)
tanh_w4_r1_case_1_safe       idem                                                     assert isgreaterequal(output_array[2],  0.0f)
tanh_w4_r2_case_0_safe       idem                                                     assert isgreaterequal(output_array[4],  0.0f)
tanh_w4_r4_case_0_safe       idem                                                     assert isgreaterequal(output_array[14], 0.0f)
```

(`tanh_w4_r3_case_0_safe` has the identical shape but was not on the wrong-result
list — presumably it times out or returns unknown rather than getting far enough to
find the spurious trace. Not investigated.)

## `filter2_alt` — SEPARATE root cause (confirmed): `static` is silently dropped

`filter2_alt` does **not** belong to the softsign/tanh family. Its cause is a
different, also pre-existing frontend bug, in the same neighbourhood.

`filter2_alt.c` declares `static float E[2], S[2];` inside `filter2()`. C gives those
static storage duration: zero-initialised once, and persisting across calls.

### Evidence A — the storage class is discarded in the frontend

`/home/coder/theta/subprojects/frontends/c-frontend/src/main/java/hu/bme/mit/theta/frontend/transformation/grammar/type/TypeVisitor.java:373-390`

```java
case "static":
    return null;      // <-- dropped entirely
```

`CSimpleType` has `extern`, `typedef`, `isVolatile`, `isThreadLocal` fields — but
**no `static` field at all** (checked
`.../transformation/model/types/simple/CSimpleType.java:28-51`). There is nowhere for
the flag to be recorded, and `grep -rn "static"` over
`.../transformation/grammar/` finds only this one site. So a `static` local is
compiled exactly like an automatic local.

### Evidence B — the serialized model re-`alloca`s E and S on every call

`--backend NONE --enable-c-serialization` on `filter2_alt.c`. The `while(TRUE)` loop
body is inlined, and this block appears at **all three** entries into the `filter2()`
body (once before the loop, once at the end of each of the two loop paths):

```
__malloc = (__malloc bvadd 3);
call_alloca_ret6 = (__malloc bvadd 1);
__malloc = (__malloc bvadd 3);
call_alloca_ret7 = (__malloc bvadd 1);
filter2__E = (+ call_alloca_ret6);
filter2__S = (+ call_alloca_ret7);
```

A **fresh base** for `E` and `S` per call, and no initialization of either. The
`INIT != 0` branch's writes to `E[0..1]`/`S[0..1]` are therefore dead — the very next
statement re-allocates both. Then the `INIT == 0` branch does

```
P = 0.4677826*X - E[0]*0.7700725 + E[1]*0.4344376 + S[0]*1.5419 - S[1]*0.674047
```

reading four cells of never-written, freshly-allocated storage, so `P` is
unconstrained and `__VERIFIER_assert(P >= -15 && P <= 15)` is violable after one
iteration. That is the spurious counterexample.

### Evidence C — both halves of the static bug reproduce standalone

| repro | code | result | correct |
|---|---|---|---|
| `static_zeroinit.c` | `int main(){ static int a[2]; if (a[1] != 0) reach_error(); }` | `Unsafe` (len 3) | Safe — statics are zero-initialised (C11 6.7.9p10) |
| `static_persist.c` | `static void f(int set,int*out){ static int a[2]; if(set) a[0]=42; else *out=a[0]; }`<br>`int main(){int o=0; f(1,&o); f(0,&o); if(o!=42) reach_error();}` | `Unsafe` (len 3) | Safe — statics persist across calls |

(`static int a[4] = {1}` → `Unsafe` is explained by *either* bug, so it is not
diagnostic on its own; `static_zeroinit.c` isolates the static bug specifically.)

### Caveat on the value of fixing filter2_alt

Fixing the static handling removes the *wrong* verdict, but filter2_alt is the
ASTRÉE ellipsoid-domain example: proving it needs a relational quadratic invariant
that EXPL/PRED CEGAR will not find. Expect `false` → `unknown`/timeout, not `true`.
In SV-COMP scoring that is still a large gain (wrong-false is heavily penalised,
unknown is 0).

### Evidence D — the verdict

`filter2_alt.c`, `--backend CEGAR --domain EXPL --architecture ILP32` →
`(SafetyResult Unsafe Trace length: 6)`. Six steps = one loop iteration, exactly the
shape the model predicts (INIT-true pass, re-alloca, INIT-false pass reads the
fresh unconstrained cells).

## BLAST RADIUS BEYOND THIS FAMILY

Files under `/home/coder/sv-benchmarks/c/` containing an aggregate of size >= 2
initialized with a single zero (`grep -rlE '\[[0-9]*[2-9][0-9]*\] *= *\{ *0(\.0[fF]?)? *\} *;'`,
`.c` + `.i`), by top-level directory:

```
416 neural-networks   104 coreutils-v8.31   74 intel-tdx-module   20 aws-c-common
 16 memsafety-cve      14 ldv-linux-3.4-simple   9 seq-pthread    2 loop-acceleration   1 sqlite
```

656 files. This is an upper bound on Bug 1's reach — it does not distinguish locals
from globals (globals are fine) and does not check whether the unwritten tail is ever
read. But the non-NN directories in that list (coreutils, intel-tdx-module,
aws-c-common, memsafety-cve) are exactly the ones where a zero-filled buffer is
normally *relied on*, so Bug 1 is very likely producing false alarms outside this
family too. Not verified beyond the NN tasks.

## MINIMAL REPRO

### Bug 1 — partial brace initializer of a local aggregate (the softsign/tanh family)

```c
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }

int main() {
    float a[4] = {0.0f};
    if (a[2] != 0.0f) { reach_error(); }   /* C: unreachable. Theta: Unsafe */
    return 0;
}
```

`(SafetyResult Unsafe Trace length: 3)` under `--memory-model multi`, `flat` and
`bytes`. Files: `scratchpad/nnwork/rep_partinit.c` (+ the variant matrix `r_*.c`).

### Bug 2 — `static` local (filter2_alt)

```c
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "t.c", 3, "reach_error"); }

int main() { static int a[2]; if (a[1] != 0) reach_error(); return 0; }   /* Unsafe */
```

and, for the persistence half:

```c
static void f(int set, int *out) { static int a[2]; if (set) a[0] = 42; else *out = a[0]; }
int main() { int o = 0; f(1, &o); f(0, &o); if (o != 42) reach_error(); return 0; }  /* Unsafe */
```

Files: `scratchpad/nnwork/static_zeroinit.c`, `scratchpad/nnwork/static_persist.c`.

## SUGGESTED FIX

### Fix 1 — zero-fill the cells a local aggregate's brace initializer does not reach

**File**
`/home/coder/theta/subprojects/frontends/c-frontend/src/main/java/hu/bme/mit/theta/frontend/transformation/grammar/function/FunctionVisitor.java`
— `visitBodyDeclaration` (the `CStruct` branch at ~line 981 and the array/scalar
branch at ~line 1065) plus its helper `flattenInitializer` (~line 905).

**Change** — mirror the global path, which is already correct:

1. Make `flattenInitializer` record `cellIndex -> CStatement` into a
   `Map<Integer, CStatement>` instead of emitting the `CAssignment` inline. It
   already computes the exact `baseOffset` literal for every scalar leaf, so the
   index is in hand.
2. After the loop over `initializerList.getStatements()`, emit one assignment per
   cell for `i in [0, cellsOf(declaration.getActualType()))`: the recorded value if
   present, otherwise the cell type's `getNullValue()`.
3. For the per-cell type, port `cellTypeAt(type, offset)` from
   `FrontendXcfaBuilder.kt` (~line 930). `FunctionVisitor.cellsOf` (line 855) already
   exists and its javadoc says it "mirrors `FrontendXcfaBuilder#cellsOf`, which the
   same-shaped global initializer uses" — so the pairing is deliberate and this is
   completing an intended symmetry, not inventing one.

**Scope guard (important):** apply only when `declaration.getInitExpr() != null`. The
`getInitExpr() == null` else-branch (which adds min/max assumptions, i.e. leaves the
object nondeterministic) is the *correct* modelling of indeterminate automatic
storage and must not be touched. This is why the fix is sound rather than an
assumption: C11 6.7.9p21 says an aggregate with *fewer initializers than members* has
its remainder initialized as if it had static storage duration — i.e. to zero. The
fix therefore only *removes* behaviours the solver currently has that real C does
not; it adds none, and it cannot mask a real bug that depends on reading
indeterminate storage, because every cell it touches is determinate by definition.

**Risks**

- **Model blow-up — the main risk.** `float w[2048] = {0};` goes from 1 assignment
  to 2048. Globals already pay exactly this cost, but a *local* is emitted per
  inlined call site / per loop iteration, which a global never is. `poly*` (96 files,
  `[1024]`/`[1025]`/`[2048]` scratch arrays) and `linear*` (8 files) will grow the
  most; expect some new timeouts there in exchange for the 7 fixed wrongs. Worth
  measuring before/after XCFA size on `poly_1024_thresh_0_safe`. If it hurts, the
  principled mitigation is a bulk zero-fill label rather than N assignments — not
  skipping the fill.
- **May yield `unknown` rather than `true` for this family.** Once the tails are
  constrained, softsign/tanh need genuine FP reasoning, and both refinements tried
  fall over on infrastructure grounds (Z3-legacy FP interpolation; Newton
  `UnsupportedOperationException`). So budget for `wrong-false → error/unknown`
  (still a big scoring gain) rather than `+7 correct-true`, unless a portfolio config
  can interpolate over floats.
- **Cannot introduce new false alarms.** Constraining previously-free cells only
  removes traces.
- **Does NOT fix `char s[8] = "ab";`** — see the separate note below.

### Fix 1b — `char s[N] = "short string";` as a local (related, distinct)

A string-literal initializer is not a `CInitializerList`, so it falls through to
`emitInitAssignment`, which assigns the literal to the array *variable* rather than
filling its cells. The serialized model for a local `char s[8] = "ab";` contains
**no initialization statements at all** — `s[0]` and `s[1]` are unconstrained too,
not just the NUL padding. Same method, different branch. This is a plausible
contributor to the known "alloca-string false-deref" family in
`benchmark-results/PLAN.md` — worth checking there; not verified here.

### Fix 2 — honour the `static` storage class (filter2_alt)

**Files**
- `.../frontend/transformation/grammar/type/TypeVisitor.java:381` — `case "static":
  return null;` currently drops it. Record it instead (add an `isStatic` flag to
  `CSimpleType` next to `extern`/`typedef`/`isThreadLocal`; there is no such field
  today).
- `.../grammar/function/FunctionVisitor.java:visitBodyDeclaration` — for a static
  local, skip the per-call `alloca` + initializer emission and instead register the
  object once through the global path
  (`FrontendXcfaBuilder.initializeGlobalVariable`), which already zero-fills
  correctly and already handles the no-initializer case as zero.

**Risks**

- Names must be mangled per function (and per block, for shadowing) or two functions
  declaring the same static name collide.
- File-scope `static` means *internal linkage*, not a storage-duration change: the
  new flag must only alter local-declaration handling. `static` on a function
  definition also reaches `visitStorageClassSpecifier` and must stay a no-op.
- Hoisting makes the object genuinely shared, which is correct — but the data-race
  checker will now see it. New race reports may be correct; false ones are possible
  if the atomicity/object-storage registration is not done the way the global path
  does it (`recordObjectAtomicity`, `giveStructObjectStorage`).
- Bigger change than Fix 1, and for filter2_alt itself the payoff is only `false` →
  `unknown` (it is the ASTRÉE ellipsoid example; EXPL/PRED CEGAR will not prove it).

**Priority:** Fix 1 is small, precedented, and worth the 7 wrong results. Fix 2 is
larger and worth 1 here plus whatever else in the suite uses static locals.

## CONFIDENCE

- Bug 1 is the cause of the 7 softsign/tanh false alarms — **high**. Four independent
  lines of evidence: the missing writes are directly visible in the serialized model;
  a 6-line repro reproduces on all three memory models; the local/global asymmetry is
  visible in both the model and the source; and spelling the tails out in the real
  task makes the counterexample disappear.
- All 7 share one cause — **high** (identical declarations and assertion shape).
- cartpole/poly are unaffected for the stated reason — **high** (cartpole has zero
  partial initializers; poly's are all length-1 or fully overwritten before read).
- `filter2_alt` is a *different* cause (`static` dropped) — **high** (the frontend
  discards the keyword with no field to hold it; the model shows the per-call
  re-alloca; both halves reproduce standalone).
- The suggested fixes are correct in direction — **high**. Their *cost* (model
  blow-up, whether the family reaches `true` or only `unknown`) — **low/medium**; the
  FP-interpolation wall is real and unmeasured beyond two failed refinements.

## ANYTHING I COULD NOT DETERMINE

1. **No positive `Safe` on the zero-filled softsign variant.** The spurious
   counterexample provably disappears, but I could not get the checker to *prove* the
   fixed program. Both refinements available to me fail for reasons unrelated to this
   bug: `--refinement SEQ_ITP` → `Z3ItpSolver.getInterpolant: theory not supported by
   interpolation or bad proof`; `--refinement NWT_IT_WP` →
   `ExprTraceNewtonChecker$1.visit: UnsupportedOperationException`. So I can state
   "the false alarm is caused by the missing zero-fill" with high confidence, but not
   "fixing it makes these 7 tasks correct-true" — they may land on `unknown`.
   (Untried: `PRED_CART`, `BOUNDED`/`KIND`, a non-Z3-legacy refinement solver. I did
   not want to burn more shared-box time on it once the direction was clear.)
2. **Why `tanh_w4_r3_case_0_safe` is not on the wrong list** though it is structurally
   identical to the other 7. Presumably timeout/unknown; not investigated.
3. **Whether the w8/w16/w32/w64 softsign/tanh tasks are wrong too, or just slow.**
   They have the same declarations with wider arrays. Not run.
4. **The real cost of Fix 1.** I did not measure XCFA size before/after on a
   `[2048] = {0}` case (poly), so the timeout risk is stated but unquantified.
5. **Whether Bug 1 explains false alarms in coreutils / intel-tdx-module /
   aws-c-common / memsafety-cve.** The pattern is present in 218 files there (see
   BLAST RADIUS) and the shape is right, but I verified nothing outside
   `neural-networks`.
6. **Fix 1b (`char s[N] = "short";`) is confirmed as a bug** (no init statements
   emitted at all) but I did not confirm it is the cause of the known alloca-string
   false-deref family in `PLAN.md` — only that it is a strong candidate.
7. A minimal float RNN-cell repro pair (`rnn_bug.c`/`rnn_fixed.c`) was written but
   abandoned: CEGAR EXPL over floats exceeded 6 min on both, and `rep_partinit.c` is
   already decisive for the mechanism.

## Ruled out

- **A regression from `7de55d4797` (AllocaFunctionPass).** Ruled out: the missing
  zero-fill is in `FunctionVisitor.visitBodyDeclaration`, which that commit does not
  touch, and the 6-line repro `float a[4] = {0.0f}` has nothing to do with the
  double-remove bug that commit fixed. The commit only stopped the frontend from
  crashing, which un-masked a pre-existing modelling bug — exactly as the assignment
  suspected.
- **A memory-model-specific bug.** Ruled out: `rep_partinit.c` is `Unsafe` under
  `multi`, `flat` *and* `bytes`.
- **Anything specific to floats, `isgreaterequal`, `fabsf`, or the FP CastVisitor.**
  Ruled out: the same bug reproduces with `int a[4] = {1}`.
- **The function pointers (`k2c_activationType *`).** They do force this task off
  `--memory-model multi` onto `flat` (the frontend prints the fallback note), but they
  are not the cause: the bug is present under `multi` too, and cartpole/poly-style
  function-pointer use without partial initializers does not false-alarm.
- **cartpole/poly sharing the cause.** Ruled out: cartpole has zero partial
  initializers; poly's are all length-1 or fully overwritten before being read, and
  its biases are spelled out in full.
- **`filter2_alt` sharing the cause.** Ruled out: its arrays have *no* initializer at
  all, so Bug 1's code path is never entered. Its cause is the dropped `static`.
