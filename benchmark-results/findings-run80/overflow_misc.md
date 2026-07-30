# Run-80 wrong-result triage: no-overflow / memleaks / SB / termination

Status: IN PROGRESS (written incrementally). All evidence from the prebuilt dist
`/home/coder/theta/subprojects/xcfa/xcfa-cli/build/distributions/Theta-svcomp`, no rebuild.

## Exact wrong list (run 80) for my families

```
no-overflow  MISSED BUG (says true, expect false):
  array-memsafety/add_last-alloca-1        (ILP32)
  array-memsafety/stroeder1-alloca-1       (ILP32)
  array-memsafety/stroeder2-alloca-1       (ILP32)
  ldv-regression/test22-2                  (ILP32)
  termination-crafted/Stockholm-2          (LP64)
  termination-nla/dijkstra6-both-nt        (ILP32)
no-overflow  FALSE ALARM (says false(no-overflow), expect true):
  busybox-1.22.0/dirname-1                 (LP64)
  aws_ring_buffer_acquire_harness
  array-memsafety/cstrcspn_reverse_alloca
  array-memsafety/cstrlen_reverse_alloca
  array-memsafety/cstrspn_reverse_alloca
  array-memsafety/openbsd_cstrstr-alloca-1
valid-memsafety FALSE ALARM (all 6 are false alarms, none is a missed bug):
  ldv-memsafety/memleaks_test11    -> false(valid-deref)
  ldv-memsafety/memleaks_test20-2  -> false(valid-free)
  ldv-memsafety/memleaks_test21-2  -> false(valid-free)
  ldv-memsafety/memleaks_test22_1-2 -> false(valid-deref)
  ldv-memsafety/memleaks_test22_2-2 -> false(valid-deref)
  ldv-memsafety/memleaks_test22_3-1 -> false(valid-deref)
unreach-call MISSED BUG:
  memory-model/2SB, memory-model/4SB
termination FALSE ALARM:
  32_1_cilled_...nettel.ko..., 43_1a_cilled_...nettel.ko...
```

---

# FAMILY 1a — no-overflow missed bugs in *additive chains* (`Stockholm-2`, `dijkstra6-both-nt`)

**SIZE** 2 confirmed here; the same defect very likely also contributes to others.
**DIRECTION** missed bug (theta `true`, expected `false`).

## ROOT CAUSE (high confidence, proven from the serialised model)

Theta emits **exactly one range check per `AddExpr` node**, but the C frontend collapses a
whole C additive *chain* `e0 ± e1 ± e2 ± …` into a **single n-ary `Add`**. C semantics is
left-associative binary (`((e0±e1)±e2)±e3`) and **each** intermediate result must be in range.
The intermediate results have no node in the model, so they are never checked. A program whose
*final* sum is in range but whose *intermediate* sum overflows is reported safe.

Two independent code sites produce the flattening:

1. `subprojects/frontends/c-frontend/src/main/java/hu/bme/mit/theta/frontend/transformation/grammar/expression/ExpressionVisitor.java:499` `visitAdditiveExpression`:
   it maps *all* `multiplicativeExpression()` children into one list and builds
   `AbstractExprs.Add(collect)` — one node, one `cType` metadata entry, for the entire chain.
   Subtraction becomes `Neg` of the operand (`castTo = AbstractExprs.Neg(castTo)`, line 525).
2. `subprojects/common/core/src/main/java/hu/bme/mit/theta/core/utils/ExprSimplifier.java:763`
   `simplifyIntAdd` (and the Bv/Rat twins) additionally **flattens nested `Add`s**:
   `if (opVisited instanceof IntAddExpr) ops.addAll(addOp.getOps())`. `SimplifyExprsPass` runs
   twice *before* `OverflowDetectionPass` in `ProcedurePassManager.kt`, so even a properly
   nested chain would be flattened before instrumentation.

`OverflowDetectionPass.kt` then does `label.getExpressions { it is AddExpr || … }` and emits one
`Not(limitVisitor(...))` per matched node → one check for the whole chain.

### Second, separate defect at the same site: the `Neg` has no `cType`

In `visitAdditiveExpression` the metadata is created for the *operand* (`exprs.get(i)`) and for
the *final* `add`, but **not for the `Neg` wrapper**. `OverflowDetectionPass`'s filter is
`it is NegExpr && metadata["cType"] is CInteger && isSsigned`, and `orElse(false)` when the
metadata is absent — so **`-x` produced by a C subtraction is never overflow-checked**, i.e.
`- INT_MIN` inside a subtraction is invisible even as a unary negation.

## EVIDENCE

`Stockholm-2` serialised model (`--enable-c-serialization`, the loop body edge):

```
__overflow__78__tmp:
  case 0: if(!(! (((main__x + main__a + (- main__b) + -1) >= -2147483648)
                && ((main__x + main__a + (- main__b) + -1) <= 2147483647)))) abort();
          goto main_error;
  case 1: ... main__x = (main__x + main__a + (- main__b) + -1);
```

Only the *total* `x + a + (-b) + (-1)` is range-checked. Native proof that the real program
overflows at an intermediate (x=INT_MAX, a=b=1, which satisfies the guard `a == b`):

```
$ gcc -fsanitize=signed-integer-overflow st.c && ./st     # int x=2147483647,a=1,b=1; x+a-b-1
st.c:2:51: runtime error: signed integer overflow: 2147483647 + 1 cannot be represented in type 'int'
st.c:2:55: runtime error: signed integer overflow: -2147483648 - 1 cannot be represented in type 'int'
2147483646        <-- final value is in range, so theta's single check passes
```

`dijkstra6-both-nt` serialised loop condition `p*p - n*q + q*r == 0`:

```
(! ((main__p * main__p)            in range))
|| (! ((main__n * main__q)         in range))
|| (! ((main__q * main__r)         in range))
|| (! (((main__p*main__p) + (- (main__n*main__q)) + (main__q*main__r)) in range))
```

The three `Mul`s are each checked (the multiplicative visitor builds a *binary* chain, so those
nodes exist) — but `- (n*q)` is **not** checked (no `cType` on the `Neg`) and the intermediate
`p*p - n*q` does not exist. With `n = INT_MIN`, `p=0, q=1, r=n`: `p*p=0` ok, `n*q=INT_MIN` ok,
`q*r=INT_MIN` ok, total `0 + 2147483648 + (-2147483648) = 0` ok → theta reports safe. Native:

```
$ gcc -fsanitize=signed-integer-overflow dij.c && ./dij   # n=INT_MIN;p=0;q=1;r=n; p*p-n*q+q*r
dij.c:2:63: runtime error: signed integer overflow: 0 - -2147483648 cannot be represented in type 'int'
dij.c:2:55: runtime error: signed integer overflow: -2147483648 + -2147483648 ...
0                 <-- final value in range again
```

The violation is on the **first** evaluation of the loop condition, so this is not a
search-depth problem — the property is simply not instrumented there.

## MINIMAL REPRO

```c
extern int __VERIFIER_nondet_int(void);
int main() {
  int x = __VERIFIER_nondet_int();
  int a = __VERIFIER_nondet_int();
  return x + a - a;            /* (x+a) overflows for x=INT_MAX,a=1; total == x */
}
```
`theta-start.sh … --property no-overflow.prp` reports Safe; gcc's UBSan reports the overflow.
Any 3-or-more-term additive chain, or any C subtraction whose negated operand is `INT_MIN`,
reproduces it.

## SUGGESTED FIX

Primary (frontend, `ExpressionVisitor.visitAdditiveExpression`, ~line 499-534): build the chain
**left-associatively as binary `Add`/`Sub` nodes**, giving each intermediate its own `cType`
metadata — mirroring what `visitMultiplicativeExpression` already does. That makes every C-level
intermediate a checkable node.

Then `OverflowDetectionPass` needs the flattening in `ExprSimplifier.simplifyIntAdd` /
`simplifyBvAdd` to not undo it. Options, cheapest first:
 * run `OverflowDetectionPass` **before** the two `SimplifyExprsPass` invocations (the pass ends
   with its own `SimplifyExprsPass(...)` call, so ordering is already assumed to be flexible) —
   but it currently relies on inlining/LBE having happened, so this is not a free move; or
 * make the metadata-carrying nodes opaque to flattening (e.g. skip the `ops.addAll(addOp.getOps())`
   merge when the inner `Add` carries a `cType` metadata entry). This is the surgical version.

Secondary and independent, cheap and worth doing regardless: attach `cType` metadata to the
`Neg` created at `ExpressionVisitor.java:525` so unary-minus overflow (`-INT_MIN`) is checked.

**Risk.** Both changes strictly *add* overflow checks, so they can only turn `true` into
`false(no-overflow)` — expect new false alarms wherever the intermediate range check is too
coarse, and a real cost in CEGAR precision/time (every additive chain becomes N branch points
instead of 1, so `no-overflow` tasks get more locations and more refinement work). The `Neg`
metadata change also affects `NegExpr`s created elsewhere only if they share the node, which they
do not. Under `--arithmetic bitvector` the `bvOverflowCondition` path (`BvOverflow.kt`) must be
checked to handle binary Sub/Neg correctly, not just n-ary Add.

**CONFIDENCE: high** for the root cause and the evidence; medium on the best fix shape (the
simplifier-flattening interaction needs care).

---

# FAMILY 1b — no-overflow missed bug in `test22-2`: **`ReferenceElimination` silently deletes *all* overflow instrumentation from the procedure**

**SIZE** 1 confirmed in this family, but the defect is a *general soundness hole* that can silently
disable the whole `no-overflow` property (and anything else keyed on `cType`) for any procedure that
takes the address of a struct member through a pointer.
**DIRECTION** missed bug (theta `true`, expected `false`).

## ROOT CAUSE (high confidence, minimal repro + code path both confirmed)

`test22-2.c`'s serialised model contains **zero** overflow checks — not one `__overflow__*` location.
Both violating operations are present but unguarded:

```
main__i = (main::pd3[0] + -10);      /* INT_MIN - 10 : real overflow, NOT checked */
main__i = (main__i + 1);             /* ++i          : NOT checked */
```

Compare `dijkstra6` (same run, same options), which is full of `__overflow__NN__tmp` locations. So
`OverflowDetectionPass` ran (it had removed the reach_error incoming edges — `main_error` is
unreachable and the old ERROR block became the self-loop `__loc_187: goto __loc_187;`) and simply
**found nothing to instrument**.

The chain:

1. `cType` metadata is stored in
   `subprojects/frontends/c-frontend/src/main/java/hu/bme/mit/theta/frontend/FrontendMetadata.java:56`
   keyed by `Tuple2.of(expr, System.identityHashCode(expr))` — effectively an **identity** map.
   Rebuilding an expression, even into a structurally identical one, loses its `cType`.
2. `OverflowDetectionPass.kt` only instruments nodes whose `cType` is a signed `CInteger`
   (`.orElse(false)`), so a lost `cType` means **silently no check** — no warning, no error.
3. `int *pa = &pd1->a;` is a reference-to-dereference, which makes
   `ReferenceElimination.runComplexReferenceElimination`
   (`subprojects/xcfa/xcfa/src/main/java/hu/bme/mit/theta/xcfa/passes/ReferenceElimination.kt:481`)
   fire. Once it has any split var it rewrites **every edge of the procedure**:
   ```kotlin
   val edges = LinkedHashSet(builder.getEdges())
   for (edge in edges) {
     builder.removeEdge(edge)
     builder.addEdge(edge.withLabel(edge.label.changeComplexReferredVars(splitVars)))   // :503
   }
   ```
4. `Expr<T>.changeComplexReferredVars` (`ReferenceElimination.kt:1171`) ends with an
   **unconditional rebuild and no metadata propagation**:
   ```kotlin
   val ret = this.withOps(this.ops.map { (it as Expr<Type>).changeComplexReferredVars(splitVars) })
   return ret as Expr<T>
   ```
   So every arithmetic node in the procedure — including ones that have nothing to do with pointers —
   comes out as a fresh object with no `cType`.

The asymmetry is decisive: the **simple** reference-elimination path in the *same file* does carry
the metadata across the rebuild (`ReferenceElimination.kt:1290-1307`):
```kotlin
if (parseContext?.metadata?.getMetadataValue(this, "cType")?.isPresent == true) {
  parseContext.metadata.create(ret, "cType", CComplexType.getType(this, parseContext))
}
```
The complex path was never given the same treatment.

## EVIDENCE / BISECTION

Bisecting the real task (`--backend NONE --enable-c-serialization`, ILP32):

| variant | change | `__overflow__` locations |
|---|---|---|
| `test22-2.c` as-is | — | **0** |
| v1 | `while (i < *pa) {++i;}` deleted, `int *pa = &pd1->a;` kept | **0** |
| v2 | `int *pa = &pd1->a;` deleted, `*pa` → `pd1->a` | **4** |

So it is the `&pd1->a` line, not the loop, that removes the instrumentation.

## MINIMAL REPRO (14 lines, `--property no-overflow.prp --architecture ILP32`)

```c
extern int __VERIFIER_nondet_int(void);
extern _Bool __VERIFIER_nondet_bool(void);
struct S { int a, b; };
struct S s1, s2;
struct S *pick() { return __VERIFIER_nondet_bool() ? &s1 : &s2; }
int main() {
  int k = __VERIFIER_nondet_int();
  struct S *p = pick();
  int *pa = &p->a;        /* <-- delete this line (and use p->a below) */
  int m = k - 10;         /* MUST be overflow-checked */
  return m + *pa;
}
```
With the `int *pa = &p->a;` line: **0** overflow-check locations in `xcfa.c`.
Without it: **2**. (Files kept at
`/tmp/claude-568/-home-coder-theta/9900e6ae-2a7e-4bd5-8035-b832459e61c7/scratchpad/work/r/d_yes.c`
and `d_no.c`.)

## SUGGESTED FIX

`subprojects/xcfa/xcfa/src/main/java/hu/bme/mit/theta/xcfa/passes/ReferenceElimination.kt`, the
`changeComplexReferredVars` family: propagate `cType` onto every rebuilt node exactly as the simple
`changeReferredVars` path already does at lines 1290-1307 — i.e. before returning `ret`, if `this`
had a `cType`, `parseContext.metadata.create(ret, "cType", <same type>)`. `ReferenceElimination`
already holds `parseContext`, so no signature change is needed for the top-level entry, but the
private `changeComplexReferredVars` helpers would need it threaded through (they currently do not
take it).

A cheap belt-and-braces companion: in `OverflowDetectionPass`, a missing `cType` on an
`Add/Sub/Mul/Div/Neg/ShiftLeft` node of integer/bitvector type is *always* a bug — log it through
`uniqueWarningLogger` instead of `orElse(false)`. That would have made this visible immediately
instead of it costing a wrong result.

**Risk.** Restoring the metadata *adds* overflow checks, so it can only flip `true` →
`false(no-overflow)`; the exposure is new false alarms and more CEGAR work on every task that
contains a `&p->member`. It also makes `CComplexType.getType` succeed in places where it currently
throws/defaults, so other `cType`-driven code (`MemsafetyPass`, `HavocPromotionAndRange`,
`BvOverflow`) starts seeing types it did not see before — that is the direction of *more*
soundness but it is a behavioural change beyond the overflow property, so it wants its own
benchmark run rather than being folded in with 1a.

**CONFIDENCE: high.**

---

# FAMILY 1b (extended) — the SAME defect explains `add_last-alloca-1`, `stroeder1-alloca-1`, `stroeder2-alloca-1`

**SIZE** these 3 + `test22-2` = **4 of the 6** no-overflow missed bugs, one root cause.
**DIRECTION** missed bug.

## Why the alloca tasks are 1b and NOT the coordinator's pointer/alloca `valid-deref` bug

The trigger *overlaps* (a pointer that undergoes pointer arithmetic on an `alloca`'d buffer, which
makes `ReferenceElimination` split it into `base`/`offset`), but the **defect is different and the
fix is in a different place**: here the split does not compute a wrong address — it *destroys the
`cType` metadata of every expression in the procedure*, so `OverflowDetectionPass` emits **no
checks at all** and the property becomes vacuously true. Nothing about the address arithmetic
needs to be wrong for this to produce a wrong `true`. So this is not a duplicate of the
`valid-deref` investigation, though both live in `ReferenceElimination.kt`.

## EVIDENCE — overflow-check count per task (`--backend NONE --enable-c-serialization`, ILP32)

| task | `__overflow__` locations | split vars in model |
|---|---|---|
| `dijkstra6-both-nt` (no pointers) | many | none |
| `add_last-alloca-1` | **0** | `main__a_base`, `main__a_offset` |
| `stroeder1-alloca-1` | 1 (in `main` only) | `sumOfThirdBytes__p_base/_offset` |
| `stroeder2-alloca-1` | 1 (in `main` only) | `sumOfThirdBytes__p_base/_offset` |
| `test22-2` | **0** | `main__if0__then1__pa_base` |

`stroeder1`/`stroeder2` are the cleanest proof, because `ReferenceElimination` is **per procedure**:
`main` (no split) keeps its metadata and gets its one check (`main__for3__i + 1`), while
`sumOfThirdBytes` (where `p = &numbers[i]` splits `p`) loses all of it — the actual violating
operations are emitted bare:

```
/* stroeder1, sumOfThirdBytes -- no check on either line */
sumOfThirdBytes__sum    = (sumOfThirdBytes__sum + sumOfThirdBytes::p_base[sumOfThirdBytes::p_offset]);
sumOfThirdBytes__i      = (sumOfThirdBytes__i + 1);
/* stroeder2 -- likewise */
sumOfThirdBytes__sum = (sumOfThirdBytes__sum + 1);
sumOfThirdBytes::p_base[...] = (sumOfThirdBytes::p_base[...] - 1);
```

`add_last-alloca-1`: the whole program is `main`, `a` is split, so **every** arithmetic op is bare,
including the actual violation `*a += *(arr + length - 1)`:

```
main::a_base[main::a_offset] = (main::a_base[main::a_offset] + main::arr[(mod (+ (mod main::length 4294967296) -1) 4294967296)]);
main__a_offset = (main__a_offset + 1);
main__for4__k  = (main__for4__k + 1);
```
That first line is `arr[0] + arr[1]` with both elements `__VERIFIER_nondet_int()` — an overflow
reachable in two loop iterations with `length == 2`. Nothing checks it.

Side note worth its own ticket (not the cause of these verdicts): in `stroeder1/2` the C is
`char *p = (char*)&numbers[i]; p = p + 2; ... *p ...`, and the model emits
`p_offset = p_offset + 2` on an **int-cell**-indexed offset, i.e. it reads `numbers[i+2]` as a
whole `int` instead of byte 2 of `numbers[i]`. So `char*` arithmetic is being scaled in element
units under `--memory-model multi`. That is a separate (and also unsound) modelling gap.

## MINIMAL REPRO — one line flips instrumentation from 4 checks to 0

```c
extern int __VERIFIER_nondet_int(void);
int main() {
  int n = __VERIFIER_nondet_int();
  if (n < 1 || n > 100) n = 1;
  int *arr = (int*)__builtin_alloca(n * sizeof(int));
  int k = __VERIFIER_nondet_int();
  int m = k - 10;                 /* MUST be overflow-checked */
  int *a = &arr[0]; a++; *a += m; /* <-- forces base/offset split */
  return m;
}
```
```
e_nosplit.c (arr[1] += m; instead)  -> 4 __overflow__ locations, no split vars
e_split.c   (as above)              -> 0 __overflow__ locations, a_base/a_offset present
```
(kept at `…/scratchpad/work/r/e_split.c`, `e_nosplit.c`)

The split-discovery site is `ReferenceElimination.discoverSplitVars` (line 620) /
`globalSplitVars` (585), which split any variable assigned a `Reference(Dereference(...))`
(`&arr[i]`, `&p->field`) and transitively anything copied from such a variable. Once
`splitVars` is non-empty, `runComplexReferenceElimination` (481) rewrites **every** edge of the
procedure through `changeComplexReferredVars`, whose `Expr` case (1171) is a bare
`withOps(...)` with no metadata propagation.

**SUGGESTED FIX**: identical to 1b above — propagate `cType` in `changeComplexReferredVars`.
Note this single fix should recover `test22-2`, `add_last-alloca-1` and possibly the two
`stroeder` tasks (those additionally need the search to reach the overflow, which looks easy
given the model reads a full `int`), i.e. up to 4 wrong results.

**CONFIDENCE: high** (mechanism, per-procedure discrimination, and a one-line minimal repro).

