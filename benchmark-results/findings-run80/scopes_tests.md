# `scopes*` / `test-*` / `nested_structure_noptr` valid-memsafety wrongs

STATUS: work in progress (written incrementally). Last update: initial dump of confirmed
evidence for the false-alarm subgroup.

Prebuilt dist used: `/home/coder/theta/subprojects/xcfa/xcfa-cli/build/distributions/Theta-svcomp`
(contains eca4430225, the global-split fix). All tasks are ILP32.

## FAMILY / SIZE / SPLIT (confirmed from the .yml files)

19 tasks, all under `valid-memsafety`.

### false alarms — theta `false`, expected `true` (12)
| task | path |
|---|---|
| nested_structure_noptr-1 | c/ldv-regression/nested_structure_noptr-1.i |
| nested_structure_noptr-2 | c/ldv-regression/nested_structure_noptr-2.i |
| test-0504 | c/memsafety/test-0504.i |
| test-0504_1 | c/list-ext-properties/test-0504_1.i |
| test-bitfields-2-2 | c/ldv-memsafety-bitfields/test-bitfields-2-2.i |
| test22-1 | c/ldv-regression/test22-1.c |
| test25-2 | c/ldv-regression/test25-2.c |
| test26-1 | c/ldv-regression/test26-1.c |
| test27-1 | c/ldv-regression/test27-1.c |
| test30-1 | c/ldv-regression/test30-1.c |
| scopes4-1 | c/memsafety-ext3/scopes4-1.c |
| 960521-1_1-2 | c/list-ext-properties/960521-1_1-2.i |

### missed bugs — theta `true`, expected `false` (7)
| task | subproperty | path |
|---|---|---|
| scopes1 | valid-deref | c/memsafety-ext3/scopes1.c |
| scopes3 | valid-deref | c/memsafety-ext3/scopes3.c |
| scopes5 | valid-deref | c/memsafety-ext3/scopes5.c |
| cmp-freed-ptr | valid-free | c/memsafety/cmp-freed-ptr.i |
| derefInLoop1 | valid-deref | c/memsafety-ext3/derefInLoop1.c |
| getNumbers1-1 | valid-deref | c/memsafety-ext3/getNumbers1-1.c |
| sum_array-2 | valid-deref | c/loops/sum_array-2.i |

`test25-2` and `test27-1` also have `expected_verdict: true` for unreach-call (both are
also wrong there — same false counterexample, since MemsafetyPass is not involved in the
unreach-call config, see open question below).

## Background: what the model looks like

Both memory models keep a global map `__theta_ptr_size : base -> size` and
`MemsafetyPass.annotateDeref` guards every `Dereference(array=B, offset=O)` with

```
B <= 0  ||  __theta_ptr_size[B] <= O  ||  O < 0     ==>  __THETA_bad_deref
```

So the check is only sound if `deref.array` is **exactly an object base id** and
`deref.offset` is an in-object offset. `MemsafetyPass` is pass-group 106 in
`ProcedurePassManager.kt`; `FlatMemoryPass` (which folds `(deref B O)` into
`(deref 0 B+O)`) is group 139 — i.e. memsafety sees the *unfolded* form.

Object base ids are partitioned mod 3: `3k+0` malloc, `3k+1` alloca/static, `3k+2`
address-taken local. Under `--memory-model flat` a base is `id * 65536`.

## CONFIRMED ROOT CAUSE A — nested struct initializer flattened onto the outer object

Tasks: **nested_structure_noptr-1, nested_structure_noptr-2** (both are the same program).

Source:
```c
typedef struct Toplev { int a; struct Inner { int b; struct Innermost { int c; } y; } x; } Stuff;
int main() { struct Toplev good = { 1, {2, {3}} }; good.x.y.c = 4; __VERIFIER_assert(good.x.y.c == 4); }
```
No pointers, no address-of, no heap — yet theta returns `(Property valid-deref) (SafetyResult Unsafe Trace length: 7)`.

Evidence — `--enable-xcfa-serialization` (`xcfa.dot`):
```
main_init -> loc94 : __malloc:=0; ptr_size:=(default 0); __malloc+=3; main::good := __malloc+1;
                     ptr_size[good] := 2;  __malloc += 3
loc94  -> loc96    : memassign (deref good 1) := __malloc+1 ; ptr_size[that] := 2 ; __malloc += 3
loc96  -> __loc_52 : memassign (deref (deref good 1) 1) := __malloc+1 ; ptr_size[that] := 1
__loc_52 -> __loc_54 : memassign (deref good 0) := 1        # good.a  = 1   OK
__loc_54 -> __loc_56 : memassign (deref good 1) := 2        # good.x.b = 2  WRONG (clobbers the sub-object pointer!)
__loc_56 -> __loc_64 : memassign (deref good 2) := 3        # good.x.y.c = 3 WRONG (offset 2 of a 2-cell object)
__loc_56 -> __THETA_bad_deref : assume (ptr_size[good] <= 2)   # 2 <= 2  -> TRUE
```
`ptr_size[good] == 2` (the outer struct has 2 members: `a`, `x`), so the guard
`ptr_size[good] <= 2` fires and the trace `main_init, loc94, loc96, __loc_52, __loc_54,
__loc_56, __THETA_bad_deref` is exactly **7 states** — matching the reported trace length.

So: a *nested* struct is modelled as a separate object reachable through a pointer stored
in the parent's cell (`good.x.y.c` is correctly read back later as
`(deref (deref (deref good 1) 1) 0)`), but the **initializer list** `{1, {2, {3}}}` is
written out **linearly** as `good[0]=1; good[1]=2; good[2]=3`. It must instead recurse
into the sub-objects: `good[0]=1; (*good[1])[0]=2; (*(*good[1])[1])[0]=3`.
Two independent faults follow: the sub-object pointer in `good[1]` is overwritten with `2`
(a soundness bug in its own right — a later read through it would address object id 2),
and `good[2]` is out of bounds → the reported false alarm.

## CONFIRMED ROOT CAUSE B — a mid-object address ends up in `deref.array`

This is one invariant violation with two different producers.

### B1: pointer arithmetic on an array/pointer that is *not* base/offset split
Task: **scopes4-1**.
```c
int *foo2(void) { static int arr[1024]; arr[194] = 13; return arr + 1; }
int *foo(void)  { static int arr[123];  return foo2(); }
int main(void)  { int *a = foo(); printf("%d\n", *a); return 0; }
```
Evidence (`xcfa.dot`):
```
main_init : call_alloca_ret1 := __malloc+1 ; ptr_size[·] := 123  ; foo::arr  := call_alloca_ret1
            call_alloca_ret0 := __malloc+1 ; ptr_size[·] := 1024 ; foo2::arr := call_alloca_ret0
__loc_198296 -> __loc_69 : ... memassign (deref foo2::arr 194) := 13     # in bounds, fine
                           foo2_ret := (foo2::arr + 1) mod 4294967296     # <-- base lost
                           main::a  := foo2_ret
__loc_69 -> __THETA_bad_deref : assume (main::a <= 0 || ptr_size[main::a] <= 0 || 0 < 0)
```
`main::a == foo2::arr + 1`, and `__theta_ptr_size` has an entry only at `foo2::arr`, so
`ptr_size[foo2::arr + 1] == 0` → the guard fires unconditionally. (Note the two same-named
statics *are* kept apart correctly — 123 vs 1024 — so the name-collision hypothesis is
ruled out; the base ids and sizes in the dump are distinct.)

`return arr + 1;` is compiled as a plain `Add(base, 1)` rather than
`Reference(Dereference(arr, 1))`, so `ReferenceElimination.discoverSplitVars` never splits
anything and the mid-object address travels as a bare scalar across the function return.
The `seedSplitParams` doc comment in ReferenceElimination.kt admits the underlying
limitation in as many words: *"the model cannot carry a mid-object pointer across a call"*.

### B2: the `--memory-model flat` fallback, whose addresses are *always* mid-object scalars
Tasks: **test26-1, test30-1, 960521-1_1-2**.

These three (and only these three of the 12) hit the automatic
`UnsupportedPointerSplitException` → `--memory-model flat` fallback. Verified directly:
```
$ for t in ...; do theta-start.sh $t --backend NONE ... | grep -c "retrying with --memory-model flat"; done
nested_structure_noptr-1  0     test27-1        0
nested_structure_noptr-2  0     test30-1        1     <-- flat
test22-1                  0     scopes4-1       0
test25-2                  0     test-0504       0
test26-1                  1     <-- flat        test-0504_1     0
960521-1_1-2              1     <-- flat        test-bitfields-2-2 0
```
Under flat, `runFlatReferenceElimination` collapses every `Reference(Dereference(B,O))`
into the single scalar `B+O`, so `&global.b` becomes `global* + 1` and the later `*pb`
becomes `Dereference(global*+1, 0)`. But `MemsafetyPass` runs *before* `FlatMemoryPass`,
so it still reads `deref.array` as a base:

test30-1 `xcfa.dot`, with `global* = 1114112` (size 2), `a* = 720896`, `b* = 917504`:
```
__loc_154220 -> loc232 : assign assign::pa := (deref 1114112 0)   # &global.a -> correct base+offset
loc232 -> __THETA_bad_deref : assume (1114113 <= 0 || ptr_size[1114113] <= 0 || 0 < 0)
loc232 -> __loc_140215225   : assign assign::pb := (deref 1114113 0)   # &global.b -> base 1114112+1 !!
```
`ptr_size[1114113] == 0` → fires unconditionally. Same picture in test26-1
(`global* = 327680`, spurious `ptr_size[327681]`).

So under the flat model `MemsafetyPass`'s valid-deref check is systematically wrong for
every non-zero field/element offset that ever passes through a pointer value. This is
consistent with the recorded run-62 result (flat = −956 vs multi, "FLOODS 81
valid-memsafety false-derefs").

## CONFIRMED ROOT CAUSE C — `(*p).field` gets one dereference too many
Task: **test22-1**.

**Minimal repro (9 lines), verdict flips on the spelling of the member access:**
```c
extern int __VERIFIER_nondet_int(void);
struct dummy { int a, b; };
struct dummy d1;
int main() {
  d1.a = __VERIFIER_nondet_int();
  struct dummy *p = &d1;
  if ((*p).a > 0) { return 1; }   /* -> (SafetyResult Unsafe), Property valid-deref */
  return 0;
}
```
Replacing `(*p).a` with the *identical* `p->a` gives `(SafetyResult Safe)`.
XCFA for the two:
```
(*p).a  ->  (deref (deref 2 0 Int) 0 Int)      # double deref
p->a    ->  (deref 2 0 Int)                    # correct
```
and the guard that fires: `ptr_size[(deref 2 0 Int)] <= 0`, i.e. `d1.a`'s (nondet) *value*
is used as an object base id.

**Exact location.** `ExpressionVisitor.visitUnaryExpressionCast`, `case "*"`
(`subprojects/frontends/c-frontend/.../grammar/expression/ExpressionVisitor.java:1200-1238`).
It has a special case for a pointer whose pointee is a `CArray`:
```java
if (type instanceof CPointer pointerToArray
        && pointerToArray.getEmbeddedType() instanceof CArray pointeeArray) {
    Expr<?> arrayObject = Pos(originalOperand);      // identity: the object IS the pointer value
    ...
}
```
but **no** such case for a `CStruct` pointee, so it falls through to
`dereference(base, 0, structType)`. The subscript path already has the missing rule, at
`ExpressionVisitor.java:3250`, and its comment even names this bug:
```java
if (elemType instanceof CStruct && isLiteralZero(index)) {
    // p[0] on a pointer-to-struct IS the pointee object ... A cell read here would treat
    // field 0's *content* as the object's base (the p->field double-deref bug, one production over).
```
So `p[0].a` and `p->a` are right and `(*p).a` is wrong, in the same file.

## CONFIRMED ROOT CAUSE D — storing a base/offset-split pointer writes both halves to the SAME cell
Tasks: **test27-1**, and it is the second fault in **test25-2**'s neighbourhood.

**Minimal repro (8 lines):** `(SafetyResult Unsafe Trace length: 6)`, expected safe.
```c
struct C { int *p; };
int main(void) {
  int a[10];
  struct C c;
  a[1] = 42;
  c.p = &a[1];
  return *(c.p);
}
```
XCFA:
```
__loc_24 -> loc44 : memassign (deref main::a 1) := 42 ; assign __theta_ref_tmp_0_base := main::a
loc44 -> loc45    : memassign (deref main::c 0 Int) := __theta_ref_tmp_0_base   # base  -> cell 0
loc45 -> __loc_41 : memassign (deref main::c 0 Int) := 1                        # offset -> cell 0 (!)
__loc_41 -> __THETA_bad_deref : assume (ptr_size[(deref main::c 0 Int)] <= 0)
```
The two writes go to the **same** cell, so the cell ends up holding the *offset* (`1`) and
the base is lost; `ptr_size[1] == 0` → guard fires unconditionally.

test27-1 has the same shape twice (`dummy.array = &a[i-1]`, `cont.array = &dummies[1]`):
```
loc247 -> loc248     : memassign (deref main::dummy* 0 Int) := __theta_ref_tmp_0_base
loc248 -> __loc_147  : memassign (deref main::dummy* 0 Int) := __theta_ref_tmp_0_offset
loc249 -> loc250     : memassign (deref main::cont* 0 Int)  := __theta_ref_tmp_1_base
loc250 -> __loc_161  : memassign (deref main::cont* 0 Int)  := 1
```

**Exact location.** `ReferenceElimination.changeComplexReferredVars`, the
`is MemoryAssignStmt<*, *, *>` branch (`ReferenceElimination.kt:821-859`). It builds
```kotlin
val baseDeref   = deref.replaceSplitRefs(splitVars, SplitChannel.BASE)  ...
val offsetDeref = deref.replaceSplitRefs(splitVars, SplitChannel.OFFSET) ...
listOf(MemoryAssignStmt.create(baseDeref, baseExpr),
       MemoryAssignStmt.create(offsetDeref, offsetExpr))
```
The "two separate memory channels" the comment claims only materialise when the *address*
expression itself contains a split var — and in that case they are worse still (the offset
value is used as an object id, which the `containsSplitRefs` comment right below admits).
When the address is an ordinary cell (the common `struct { T *p; }` field), both derefs are
identical and the second store silently clobbers the first. There is no second channel in
the model at all: `multi` has exactly one `__theta_ptr_size` and one memory array.

## CONFIRMED ROOT CAUSE E — a local array of structs is allocated with `dim` cells instead of `dim * cellsPerElement`
Task: **test25-2** (and every `struct S a[N]` / `int a[N][M]` local).

**Minimal repro (5 lines):** `(SafetyResult Unsafe Trace length: 3)`, expected safe.
```c
struct S { int a, b; };
int main(void) { struct S arr[10]; arr[9].b = 1; return arr[9].b; }
```
XCFA:
```
main_init : call_alloca_ret0 := __malloc+1 ; ptr_size[call_alloca_ret0] := 10   # <-- 10, needs 20
            main::arr := call_alloca_ret0
__loc_19  : memassign (deref main::arr 19 Int) := 1        # arr[9].b == cell 9*2+1 == 19
__loc_19 -> __THETA_bad_deref : assume (ptr_size[main::arr] <= 19)     # 10 <= 19 -> TRUE
```
The access path is right (`ExpressionVisitor#rowOf` scales by `cellCountExpr`), only the
allocation is short. In test25-2 the loop that fills `array[j].a/.b` for `j < 10` therefore
walks off the object at `j == 5` (`__loc_86_loop5 : ptr_size[main::array] <= 10`), and the
later `array[i].b` guard is `ptr_size[array] <= 2*i+1`.

**Exact location.** `FunctionVisitor.visitBodyDeclaration`
(`subprojects/frontends/c-frontend/.../grammar/function/FunctionVisitor.java:966-968`):
```java
final var alloca = new CCall("alloca", List.of(cArray.getArrayDimension()), parseContext);
```
`getArrayDimension()` is the *outermost element count*. The correct size is the cell count,
which the sibling code in `FrontendXcfaBuilder.flatArraySize`
(`FrontendXcfaBuilder.kt:569`) already computes correctly
(`size * elementType.unitCount` for a struct element, product of dimensions for a nested
array). `FrontendXcfaBuilder.allocateStackArray` uses `flatArraySize`; the *declaration*
path in FunctionVisitor does not — that is the whole divergence.

## SUPERSEDED NOTE on cause A's location
`FunctionVisitor.flattenInitializer` (`FunctionVisitor.java:903-937`) writes every scalar
leaf of an initializer list as `Dereference(varDecl, flatCellOffset)`, numbering cells as
if nested aggregates were laid out **inline** (`cellsOf` recurses into a nested struct and
returns its `unitCount`). But the object model puts a nested struct in an object of its own
and stores only its *base id* in the parent's cell (`FrontendXcfaBuilder.allocateStackStruct`
→ one cell per field). The two disagree, which is exactly cause A. A correct
`flattenInitializer` must recurse *through* the sub-object:
`Dereference(Dereference(varDecl, fieldCell), subOffset)`.

## OLD HYPOTHESIS C text (kept for the reasoning trail)
Task: **test22-1** (and to be checked: test25-2, test27-1).

test22-1 line 37 is `if (pd1 != 0 && pd1 == pd2 && (*pd2).a > 0)`, while line 39 is
`i = pd2->a - 10` and `check()` does `s1->a == i`. In the XCFA the two spellings differ:
```
# pd2->a           (correct, single deref)
__loc_138 -> __loc_146 : assign main::i := (deref main::pd2 0 Int) + -10
__loc_78204          : assign check_ret := ite((deref check::s1 0 Int) = check::i, 1, 0)

# (*pd2).a         (WRONG, double deref)
__loc_124 -> __loc_138 : assume ... (> (deref (deref main::pd2 0 Int) 0 Int) 0) ...
__loc_124 -> __THETA_bad_deref :
   assume ( (pd1!=0 && pd1==pd2) && ( (deref main::pd2 0 Int) <= 0
                                    || ptr_size[(deref main::pd2 0 Int)] <= 0 ) )
```
`deref(pd2,0)` is `d1.a`, an unconstrained `__VERIFIER_nondet_int`. Using it as a *base*
means `ptr_size[nondet] == 0` for almost every value, so `__THETA_bad_deref` is trivially
reachable. That also explains why test22-1/test25-2/test27-1 are wrong under
**unreach-call** too: the extra dereference is created by the *frontend*, not by
MemsafetyPass, so the bogus `deref(deref(p,0),0)` value feeds the program's own
comparisons in every configuration.

TO DO: minimal repro `(*p).a` vs `p->a`; check test25-2 / test27-1 / test-0504 /
test-0504_1 / test-bitfields-2-2 dumps.

## Missed bugs — not yet investigated
Working hypotheses to test (nothing confirmed yet):
- scopes1 / scopes3 / scopes5 / derefInLoop1 — block-scoped locals are allocated once at
  procedure entry and never deallocated, so a pointer to an out-of-scope block local stays
  valid.
- getNumbers1-1 — `alloca` memory is not released at function return (`3k+1` class is
  never deallocated), so use-after-return is invisible.
- cmp-freed-ptr — each `malloc` gets a fresh base id, so `(intptr_t)x == (intptr_t)y`
  after `free(y)` is unsatisfiable and the double `free(x)` is unreachable.
- sum_array-2 — zero-length VLA `int A[M]` with `M == 0`.

---

# MISSED-BUG SUBGROUP (theta `true`, expected `false`) — 7 tasks

These need the opposite argument from the false alarms: the real violation is located in
the C, then the model is shown to have no way to reach it. All evidence is from
`--enable-xcfa-serialization` dumps under the default (`multi`) model.

## CONFIRMED ROOT CAUSE G — an object's lifetime never ends: no deallocation at scope/block/iteration exit
Tasks: **scopes1, scopes3, scopes5, derefInLoop1** (4 of the 7).

The real violations:
- `scopes1` — `{ int myNumberA = 7; myPointerA = &myNumberA; }` then `*myPointerA` after
  the block. Dereference of a pointer to an out-of-scope automatic object.
- `scopes5` — `if(1) { int a[10]; p = a; }` then `p[0] = 1`.
- `scopes3` — `for(...){ int a[10]; p = a; p[0]=1; }` then `p[0] = 2` after the loop.
- `derefInLoop1` — `for(i=0;i<2;i++){ int a[10]; if(i==0) p=a; else p[0]=1; }`: iteration 1
  writes through iteration 0's dead `a`.

Why the model cannot see them. `__theta_ptr_size[base]` is written **once, on the procedure
entry edge**, and is *only* ever cleared by `MemsafetyPass.annotateFree` at an explicit
`free`. Nothing in any pass emits a `deallocate` for an automatic object.

`scopes1` (address-taken scalars get compile-time bases 5 and 8):
```
main_init -> __loc_19 : ptr_size := (default 0); ptr_size := (5 1)(default 0); ptr_size := (5 1)(8 1)(default 0)
__loc_19 -> __loc_32  : memassign (deref 5 0 Int) := 7        # myNumberA = 7, inside the block
__loc_32 -> __loc_45  : memassign (deref 8 0 Int) := 3        # myNumberB = 3
__loc_45 -> _pre_final: assume (not (ptr_size[5] <= 0 || ptr_size[8] <= 0)) ...   # both still live
```
There is not even a location where object 5's block ends — the whole procedure has three
edges. `ptr_size[5]` stays 1 forever.

`scopes5` — the block-local array's `alloca` is *hoisted to `main_init`*, so the object is
created before its block is entered and is never released:
```
main_init -> __loc_41 : __malloc += 3; call_alloca_ret0 := __malloc+1; ptr_size[·] := 10
                        main::if0::then1::a := call_alloca_ret0 ; main::p := a mod 2^32
__loc_41 -> _pre_final: assume (not (ptr_size[main::p] <= 0)) ; memassign (deref main::p 0) := 1
```

`derefInLoop1` is the sharpest evidence that this is a *lifetime* problem and not an
aliasing one — the model does give each unrolled iteration its **own** base:
```
main_init : __malloc+=3; ret0 := __malloc+1; ptr_size[ret0] := 10; for0::a := ret0   # iteration 0
            main::p := for0::a                                                       # p = &a(0)
            __malloc+=3; ret0 := __malloc+1; ptr_size[ret0] := 10; for0::a := ret0   # iteration 1, NEW base
__loc_58_loop1 -> _pre_final : assume (not (ptr_size[main::p] <= 0)) ; memassign (deref main::p 0) := 1
```
`p` still names iteration 0's base, whose `ptr_size` is still 10 → the write is accepted.
Had iteration 0's object been deallocated at the end of its iteration, `ptr_size[p]` would
be 0 and the existing `annotateDeref` guard would have fired *unchanged*. Same for
`scopes3`, where all ten unrolled iterations allocate a fresh base and none is released.

So the check machinery is already right; the missing piece is the *deallocation events*.

## CONFIRMED ROOT CAUSE H — `alloca` memory is never released at function return
Task: **getNumbers1-1**.

Real violation: `int *array = alloca(10*sizeof(int)); ... return array;` and main then reads
`*(numbers+i)` — a use-after-return of an `alloca`'d block.

Evidence:
```
main_init : __malloc+=3; call_alloca_ret0 := __malloc+1; ptr_size[call_alloca_ret0] := 40
            getNumbers::array := call_alloca_ret0
...        : (assign getNumbers_ret getNumbers::array) (assign main::numbers ...)
__loc_89_loopN -> ... : assume (not (ptr_size[main::numbers] <= N))       # N = 0..9, all pass
```
`ptr_size[·]` is set once and never cleared, so after `getNumbers` returns the block is
still live. Note `FunctionVisitor.visitBodyDeclaration`'s own comment asserts the opposite —
*"`alloca` ... its memory is released when the function returns, not by the program"* — but
no pass emits that release. `AllocaFunctionPass` only ever calls `builder.parent.allocate`
(`AllocaFunctionPass.kt:106`); there is no `deallocate` anywhere outside
`MemsafetyPass.annotateFree`.

This is the same missing mechanism as cause G, one scope level up (procedure instead of
block), so G and H are really one design gap; I list them separately because the *trigger*
differs (block exit vs. procedure return) and a fix could plausibly land one without the
other.

**Side finding (same task, opposite direction, worth a separate note):** `alloca(40)` records
`ptr_size = 40` — the byte count used directly as a **cell** count. The object really has 10
`int` cells. So bounds through an `alloca`'d block are 4× too loose under ILP32:
`numbers[10..39]` would be accepted. This hides genuine out-of-bounds bugs on
`alloca`/`malloc`-sized-in-bytes blocks (it cannot cause a false alarm, only a missed one).

## CONFIRMED ROOT CAUSE I — allocation bases come from a monotone counter, so a freed address is never reused
Task: **cmp-freed-ptr**.

Real violation (valid-free): `y = malloc(...); adressY = (intptr_t)y; free(y); x = malloc(...);
adressX = (intptr_t)x; if (adressX == adressY) free(x); free(x);` — a real allocator may
hand the just-freed block back, so `adressX == adressY` is possible and the program then
double-frees.

Evidence:
```
main_init  : __malloc += 3 (=3); call_malloc_ret0 := __malloc; ptr_size[3] := 4; main::y := 3; adressY := y
__loc_42   : ptr_size[main::y] := 0                            # free(y)
             __malloc += 3 (=6); call_malloc_ret2 := __malloc; ptr_size[6] := 4; main::x := 6; adressX := x
__loc_68   : assume (adressX = adressY)  -> __loc_78 -> free(x)      # UNSAT: 6 != 3
__loc_68   : assume (adressX /= adressY) -> __loc_88 -> free(x)      # the only feasible path
```
`__malloc` is strictly increasing and `deallocate` only writes `ptr_size[base] := 0` — it
never returns the base to the pool. `adressX == adressY` is therefore unsatisfiable, the
first `free(x)` is unreachable, and the single remaining `free(x)` passes its guard.

## CONFIRMED ROOT CAUSE J — no check that a VLA's length is > 0
Task: **sum_array-2**.

Real violation: `unsigned int M = __VERIFIER_nondet_uint(); int A[M], B[M], C[M];` with **no**
`assume(M > 0)`. `M == 0` makes the VLA declaration itself undefined — C11 6.7.6.2p5: a
variably-modified type's size "shall evaluate to a value greater than zero" — which SV-COMP
files under `valid-deref`.

Corroboration that this (and not something inside the loops) is the intended violation:
*every* `loops/` task with `expected_verdict: false, subproperty: valid-deref` has exactly
this shape and nothing else in common —
`sum_array-1`, `sum_array-2`, `matrix-2` (`int matriz[N_COL][N_LIN]`),
`insertion_sort-1` (`int v[SIZE]`), `invert_string-2` (`char str1[MAX], str2[MAX]`, which
additionally does `str1[MAX-1]` → `str1[-1]` when `MAX == 0`), `insertion_sort-2`,
`bubble_sort-1`. All size a VLA from an unconstrained nondet with no positivity assume.

Evidence that the model cannot see it — the three VLAs are allocated with size `M` itself
and every access is guarded correctly:
```
write __theta_ptr_size call_alloca_ret4 main::M
write __theta_ptr_size call_alloca_ret5 main::M
write __theta_ptr_size call_alloca_ret6 main::M
```
With `M == 0` the object has size 0 (indistinguishable from freed/never-allocated, which is
fine), every loop `for(i=0;i<M;i++)` has zero iterations, so **no dereference happens at
all** and no guard can fire. There is no check attached to the *declaration*.

Confidence on J: **medium** — the "model cannot see it" half is certain (the dump is
unambiguous), but SV-COMP's rationale for classifying a zero-length VLA as `valid-deref` is
not documented inside the repository; I inferred it from C11 plus the fact that all seven
sibling tasks share that and only that shape. If the intended violation were something
else, the fix would be different.

## Verdicts confirmed for the missed-bug subgroup (pre-13:24 dist)
```
scopes1        --svcomp --portfolio STABLE  -> (SafetyResult Safe)
scopes5        --svcomp --portfolio STABLE  -> (SafetyResult Safe)
derefInLoop1   --svcomp --portfolio STABLE  -> (SafetyResult Safe)
getNumbers1-1  --svcomp --portfolio STABLE  -> (SafetyResult Safe)
cmp-freed-ptr  --backend CEGAR --domain EXPL -> (SafetyResult Safe)   (portfolio needs >200 s)
```
i.e. theta really does prove these safe, matching run 80. `scopes3` was not re-run (same
model shape as scopes5/derefInLoop1, dump identical in the relevant respect); `sum_array-2`
not re-run (unbounded loop over `M`, slow).
