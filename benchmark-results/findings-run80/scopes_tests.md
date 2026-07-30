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
