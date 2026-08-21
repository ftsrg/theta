# SV-COMP'27 Benchmark Triage & Remediation Plan

Run analyzed: `theta.2026-07-06_17-02-59` (Theta 7.2.5, `--svcomp --portfolio STABLE`, 36,602 runs).
All findings below were verified against **current master** where noted ("repro'd") — the key bugs are still present.

## IMPLEMENTATION STATUS (branch `svcomp27-fixes`, batch 1 — as of 2026-07-09)

Committed and verified (archive spot-checks + unit tests + 50-task parse-mode canary sweep, no regressions):
- **W1** literal `U`-suffix typing — signextension2-1/2 now give correct Safe/Unsafe (2 wrong results fixed). Also C13 hex/char-literal classification and C10 sizeof null-guard. Commit: "respect U suffix in literal typing…"
- **W3** `__VERIFIER_nondet_memory` — nondet calls with arguments now rejected loudly instead of silently dropped. Commit: "reject nondet calls with arguments…"
- **W2/AD10** `--enable-signed-wraparound` FrontendConfig flag (default off), with a CLI validation rule rejecting it together with the overflow property (verified: rejected for no-overflow, allowed for unreach-call). Commit: "add --enable-signed-wraparound flag…"
- **N4** logger `String.format` misuse fixed at all call sites (pass content as `%s` arg). Commit: "logging: pass dynamic content as format args…"
- **C9** self-referential struct field resolution (`Struct.copyOf` no longer snapshots an empty field map) — verified rule60_list.i crash → resolved. **C6** `NamedType.patch` tolerates unknown specifiers (`_Complex`, `__m128*`). Commit: "fix self-referential struct field resolution…"
- **N1 (Phase 3)** `UnresolvedInvokeToHavocPass` — calls to unresolved externs (`time`, `sin`, …) are havoced with a warning instead of crashing the analysis; verified Juliet fscanf task TIMEOUT → Safe. Commit: "havoc unresolved external calls…"
- **C2** enum constants resolve to integer values (sound: unevaluable shift-based flag enumerators stay unregistered rather than guessed). Verified SOCK_STREAM crash → resolved, values correct. Commit: "resolve enum constants…"

Test infrastructure (Phase 0): canary suite + guard set + parse/full runner live in `benchmark-results/canaries/` (untracked, alongside the run data). Regression fixtures added to `c2xcfa` tests (25enum.c, 27selfrefstruct.c) and new unit tests (CLiteralTypingTest, NondetMemoryTest, UnresolvedInvokeToHavocTest, LoggerFormatSafetyTest).

### Re-test 1 outcome (`results-new/theta27-short.2026-07-09_11-27-53`, 300s/7GB) and follow-up fix

The re-test produced **1,124 wrong results** (up from 13). Analysis (`results-new/runs-new.tsv`): only **1** previously-correct task regressed (pthread-divine/tls_basic); the rest were previously-ERROR tasks (785 timeout / 246 frontend-fail / 85 OOM) that batch 1 unlocked straight into wrong verdicts:
- **625 false→true + ~297 true→false, Juliet no-overflow**: `UnresolvedInvokeToHavocPass` havoced pointer-writing input functions (`fscanf(_,_,&data)`, `recv`, …) — the swallowed write left `data` deterministic → vacuous Safe (and mirror-image false alarms on good variants).
- **70 Juliet memsafety false-derefs**: havoced `calloc` returned an arbitrary pointer.
- **16 longjmp tasks**: setjmp/longjmp havoced despite being control flow. **6 floats tasks**: havoced `ceil/floor/round/trunc/lrint/nan`. **tls_basic**: havoced `pthread_key_*` despite `isLibraryFunction` marking them for analysis-time handling.

**Fix (committed: "xcfa: only havoc unresolved calls with integer-scalar signatures")**: the pass now skips `isLibraryFunction` labels and the setjmp/longjmp family, and havocs ONLY calls whose return is an integer scalar (or void) and whose every argument is an integer scalar or a constant-folded literal null. Everything else keeps the old leave-unresolved behavior (analysis error, never a verdict). Verified: `time(NULL)` still Safe (folding handles `(mod (mod 0 …) …)` pointer-cast wrapping); fscanf-bad → "No such method fscanf" error; tls_basic → correct true; longjmp/ceil → error not verdict; 50-task parse sweep + 12-task full-mode canaries green.

### W5 ROOT-CAUSED AND FIXED (commit: "frontend: fix p->field double dereference and sizeof of struct tags")

Two independent frontend bugs, both **pre-existing** (not introduced by batch 1), together producing the dominant false `valid-deref` / `false(unreach-call)` cluster:

1. **`p->field` emitted a double dereference.** `Dereference(a,o,T)` lowers (DereferenceToArrayPass) to `__arrays_T[a][o]` — `a` is the base, `o` the offset. `visitPostfixExpressionPtrMemberAccess` emitted `Deref(Deref(p,0),i)` = `arrays[arrays[p][0]][i]`: it read **field 0's value and used it as a base address**. For a `malloc`'d pointer that base is unallocated → spurious `valid-deref`; for reachability it read garbage → spurious `unreach-call`. (The `&s` stack case accidentally worked, which is why it went unnoticed; `.` member access already used a single deref.)
2. **`sizeof(struct Tag)` silently evaluated to 0.** A struct/union/enum *tag* is not a typedef name, builtin keyword, or variable, so every lookup in `visitUnaryExpressionSizeOrAlignOf` missed and it fell to the "sizeof got unknown type, using a literal 0" path → `malloc(0)` → zero-size object. Now resolved via the type visitor.

Proof (5-line programs, `--backend BOUNDED`): before, `struct S *p = malloc(sizeof(struct S)); p->a=1; if(p->a!=1) reach_error();` reported **Unsafe** — a wrong result on a provably safe program; after, `Safe`, while the negated variant still reports `Unsafe` (bug-finding preserved). Both new regression tests (`PtrMemberAccessTest`) fail on the pre-fix code and pass after. Known-unsafe controls (array-memsafety/bubblesort_unsafe, diff_usafe, memsafety-ext3/scopes2) still report Unsafe; 50-task parse sweep + 12-task full canaries green. `list-simple/sll2n_remove_all` unreach-call went wrong→**correct (Safe)**.

**Impact classification of the 1,124 wrong results:**
| Count | Class | Status |
|---|---|---|
| 1,017 | Juliet/longjmp/floats/tls_basic — havoc swallowing | FIXED (havoc tightening) |
| 85 | heap/list families — `p->field` double deref + `sizeof(tag)`=0 | FIXED (W5) |
| 22 | see below | OPEN |

**Spot-check of every residual class against the fixed build** (local budget 130s vs the benchmark's 300s, so "no verdict" is suggestive, not conclusive):

| Task (class representative) | Was | Now |
|---|---|---|
| Juliet `CWE401_..._calloc_01_good` (70 tasks) | false(valid-deref) | no wrong verdict ✓ |
| `weaver/popl20-min-max-dec.wvr` (4) | false(valid-deref) | no wrong verdict ✓ |
| `array-memsafety-realloc/array-realloc-2` | false(valid-deref) | no wrong verdict ✓ |
| `loop-floats-scientific-comp/loop5`, `pthread/bigshot_s`, `coreutils-v9.5-units/relpath_…` | false(unreach-call) | no wrong verdict ✓ |
| `ldv-memsafety/memleaks_test16_1` | true (false-negative) | Unknown ✓ |
| **`memsafety-ext3/getNumbers1-2`** | false(valid-deref) | **STILL WRONG** ✗ |
| **`memory-model/2SB`** | true (false-negative) | **STILL WRONG (KIND says Safe on an unsafe program)** ✗ |

### Array W5 ROOT-CAUSED AND FIXED (commit: "frontend: dereference pointer arithmetic at an offset, not a shifted base")

Distinct from the struct-pointer bug. Instrumenting the emitted model showed:
- `p[i]` → `(deref p i)` — base `p`, offset `i`. **Correct.**
- `*(p + i)` → `(deref (+ p i) 0)` — the index folded into the **base**, offset 0. **Wrong.**

Since `__theta_ptr_size` is only written at the true base (default 0 elsewhere), the check `__theta_ptr_size[p+i] <= 0` is trivially true → spurious `valid-deref`. C defines `*(p+i)` ≡ `p[i]`, so `visitUnaryExpressionCast` case `"*"` now decomposes an additive operand into (pointer base, index offset). Subtlety that cost a debugging cycle: the operand arrives wrapped in identity `Pos` casts (`Pos(Add(Pos(p), Pos(i)))`), so an `instanceof AddExpr` check silently never matched — a `stripPos` helper is required.

Verified: `*(p+i)` over a 10-element array → no longer wrong; `*(p+15)` on that array is **still reported Unsafe(valid-deref)** (bound checking preserved); `getNumbers1-2` wrong→Unknown; `sll2n_remove_all` Safe; unsafe controls (bubblesort_unsafe, diff_usafe, scopes2) still Unsafe; regression test fails pre-fix. 50-task parse + 12-task full canaries green.

### Hardening (commit: "never havoc a nondet-named call that resolves to a defined procedure")

`NondetFunctionPass` matched purely on the `__VERIFIER_nondet` name prefix, so it would havoc a call even when the program **defines** a function with that name — discarding its body. SV-COMP's `memory-model` benchmarks define `__VERIFIER_nondet_step()`, `__VERIFIER_nondet_operations()` and `__VERIFIER_nondet_headerT()` (the latter returns a *struct*, so havocing its return slot havocs the base address, not the fields). In practice `InlineProceduresPass` runs first and inlines them, so this only bites when `builder.canInline()` is false (recursive programs) — but then it is a silent under-approximation. The pass now skips any name that resolves to a defined procedure; the reserved SV-COMP intrinsics are `extern`, so they are still havoced. **Note: this did NOT fix 2SB** (its functions were already being inlined) — it is defensive hardening only.

**Remaining open (~16 expected wrong results in the next run):**
- **`memory-model/2SB` + 1 sibling (~2 tasks)**: KIND proves an expected-UNSAFE program "Safe". **Correction to an earlier note in this document: 2SB contains no `pthread_create` — it is a *sequential* program that simulates a weak-memory machine, so this is a sequential BMC false-negative, NOT an OC/concurrency issue.** Cause not yet found (the nondet-guard above ruled out one hypothesis). Next steps: check whether `reach_error()` — defined with an *empty body* — is correctly turned into an error location before inlining, and whether `__CPROVER_assume`'s `abort()` prunes the error path.
- **~14 KIND memsafety false-negatives** (`memsafety-ext3/scopes1`, `ldv-memsafety/memleaks_*`): the W4 scope-lifetime gap. **This is architectural (AD2), confirmed by reading the code**: `ReferenceElimination.addRefInitializations` allocates *every* address-taken local once at the procedure's init location — there is no per-scope allocation at all, so a scope-exit `deallocate` also needs a matching scope-entry re-`allocate` (loops re-enter blocks). Requires the design doc before implementation.
- **Array-based false `valid-deref`** (`memsafety-ext3/getNumbers1-2`, `array-memsafety-realloc`): still reproduces after the W5 fix — a *distinct* bug. Suspect the size/offset unit systems disagree: `ReferenceElimination.kt:80-91` allocates `fields.size` (element count) for structs but `allocateUnit` (=1) for everything else, while `MallocFunctionPass` records the malloc argument in **bytes** and deref offsets are **element indices**. A static-array micro-test returns Unknown rather than the false deref, so arrays decay via another path — needs its own investigation before touching the memory model.
- **~14 KIND false-negatives on memsafety** (ldv-memsafety, memsafety, memory-model `false→true`): the W4 scope-lifetime gap (Phase 1.5).
- **~10 concurrency wrongs** (weaver, goblint-regression no-data-race, pthread): MultiThread/OC-adjacent — coordinate with the separate OC PR before touching.

### ⚠️ LATENT BUG (no wrong results yet, but unsound in the *missed-bug* direction): size/offset unit mismatch

The pointer-validity model mixes **two incompatible unit systems** for the same `__theta_ptr_size[base]` array:

| Allocation site | Size recorded | Units |
|---|---|---|
| `ReferenceElimination.kt:84-87` (address-taken struct local) | `t.fields.size` | **element/field count** |
| `ReferenceElimination.kt:90` (everything else, incl. arrays) | `allocateUnit` → `1` | **element count (always 1!)** |
| `MallocFunctionPass` | the `malloc` argument, i.e. `sizeof(...)` | **bytes** |

Dereference offsets (`MemsafetyPass.annotateDeref`) are always **element/field indices** (`structType.getFields()...indexOf(accName)`, array index `i`). So the bound check `__theta_ptr_size[base] <= offset` compares indices against bytes for heap objects. **Proven directly from the emitted model** (probe on `int *a = malloc(10*sizeof(int)); a[3]=1;`):
```
(assign __theta_ptr_size (write __theta_ptr_size call_malloc_ret5 40))   <- 40 BYTES
(assume (not (... (<= (read __theta_ptr_size main::a) 3) ...)))           <- offset 3 = INDEX
```
- **Missed bugs (false negatives)**: valid indices are 0..9, but an out-of-bounds `a[15]` passes `40 <= 15` = false and is **not reported**. Every heap buffer overflow within `sizeof(elem)`× the real bound is silently accepted — likely why `valid-deref` looks "clean" on heap code while missing real CWE-121/122-style overruns. (Stack/static arrays are sized in *elements* — `int a[10]` records 10 — so `*(a+15)` there **is** correctly reported.)
- Bases are also spaced only 3 apart (`__malloc += 3` per allocation) regardless of object size, so a sufficiently large index arithmetically lands on the *next* object's base.

Fixing this requires picking ONE unit system end-to-end (offsets are indices today, so element-count is the smaller change) and updating all three allocation sites plus `sizeof`-derived malloc sizes consistently — i.e. it is part of the memory-model work (AD2/Phase 1.5, and a prerequisite for the array-W5 fix). Do **not** fix one site in isolation: making `allocateUnit` return the array length while `malloc` still records bytes would turn the current false negatives into false positives on heap arrays. Needs a regression suite covering: stack array in-bounds/out-of-bounds, heap array in-bounds/out-of-bounds, struct field access, `sizeof`-vs-index arithmetic — with *expected* verdicts, since today's "correct" heap results may be correct only by accident.

### Re-test 2 outcome (`results-now/theta27-short.2026-07-09_23-39-51`, 300s/7GB) and regression fix

25 wrong (down from 1,124). Apples-to-apples vs re-test 1 (both 300s, `results-now/runs-now.tsv` vs `results-new/runs-new.tsv`): **1,104 previously-wrong fixed**, 20 wrong in both (pre-existing), and **5 NEW regressions** (correct→wrong). The 1,109 correct→error are the intended havoc-tightening soundness trades (999 are Juliet `_good` variants that were only "correct" via unsound fscanf-havoc). Net vs the *original* run: correct 5,917→6,311, wrong 13→25 — but note the original ran at 900s while these short runs use 300s, so ~968 of the original's correct results now TIMEOUT purely from the time limit (confounder — always compare `results-now` to `results-new`, not to the 900s original).

**The 5 regressions were all one root cause** (`p->field` single-deref, commit `1999f0714`) and are now FIXED (commit: "don't double-dereference address-taken struct/array variables"): `ReferenceElimination` rewrote `&m` (address of a stack struct) to the referred-var pointer's raw value, but rewrote every *bare* read of `m` to `Deref(m*, 0)` — an extra indirection. A struct variable already denotes its own base id, so the extra box is wrong for it; the old `p->field` double-deref happened to compensate, and making `p->field` a single deref (correct for malloc) desynced the stack case. Fix: in `VarDecl.changeReferredVars`, struct/array-typed referred vars resolve to the pointer's raw value (no `Deref`), exactly matching the `&m` case; scalars keep the box (they hold a value, not a base). Verified: mtx stack-struct Safe + unsafe-variant Unsafe; heap-struct Safe + unsafe Unsafe; scalar `&x` Safe + unsafe Unsafe; `ldv-regression/mutex_lock_struct.c_1` and `test28-2` true again; the 3 memsafety regressions now error instead of `false(valid-deref)`; heap-struct W5 wins (sll2n_remove_all, rule60_list) still Safe; unsafe controls still Unsafe; regression test fails pre-fix.

⚠️ **Process note**: bisecting left `git checkout <old> -- ExpressionVisitor.java` staged in the index; a later `git add <other files>` + commit silently dropped the deref fixes from that commit. Caught by `git diff` showing an unexpected 55-line delta, repaired by amending. Lesson: after any `git checkout <ref> -- <file>` during debugging, run `git status`/`git diff --cached` before the next commit.

**Remaining wrong classes (~20, all pre-existing, unaffected by this batch):**
- ~7 MultiThread/concurrency (goblint-regression, weaver, pthread/singleton) — OC-adjacent, defer to the separate OC PR.
- ~6 PRED_CART memsafety on complex heap (list-ext3, memsafety/lockfree, Juliet CWE121) — deeper W5-family, not the struct-pointer or array-index cases already fixed; needs per-task investigation.
- ~5 KIND memsafety false-negatives (scopes1, memleaks, cmp-freed-ptr) — W4 scope-lifetime gap.
- 2 memory-model (2SB/4SB) — sequential BMC false-negative (NOT concurrency).

**→ A third full re-test is warranted** once a few more of these are addressed, OR now to confirm the 25→~20 regression fix landed cleanly. All committed fixes validated against known-unsafe controls; bug-finding intact.

### Post-re-test-2 error-reduction (C3 builtins, partial)

Current error distribution (from `results-now/runs-now.tsv`, after all wrong-result fixes) — biggest addressable frontend clusters: ParseCancellation 4,108 (grammar, Phase 4); "Only structs expected here" 1,722 (unions, AD7 architectural); "Only variable-backed functions" 1,543 (function pointers, C5 architectural); overflow bitwise 1,479 + division 831 (Phase 5); "Referencing non-variable" 1,368 (C4 `&expr`, separate PR); NPE setParent 882 (C7 asm); "No such variable" 1,643 (mostly `__builtin_*` + type-names-in-expr).

Committed clean, correctness-safe builtin wins (both intercept the callee in `visitPostfixExpression` before it's evaluated, since `__builtin_*` have no declaration and otherwise throw "No such variable"):
- **`__builtin_expect(exp,c)→exp`, `__builtin_expect_with_probability→exp`, `__builtin_constant_p→0`** — exact/conservative semantics, zero wrong-result risk. Commit: "model pure-passthrough builtins".
- **`__builtin_isnan/isinf/isfinite/isnormal`** aliased to the plain library names that `FpFunctionsToExprsPass` already models exactly (emit a `CCall` with the stripped name). Verified safe+unsafe. Commit: "alias __builtin_ fp classification…".

Additional committed C3 builtin wins (all via `handleBuiltinCall` intercepting the callee before it's evaluated; all validated safe+unsafe; canary sweeps green):
- **`__builtin_isgreater/isgreaterequal/isless/islessequal/islessgreater/isunordered`** — added NaN-aware handlers to `FpFunctionsToExprsPass` (the SMT FP comparison operators already return false on NaN, matching the C macro semantics). This **also correctly models the plain `isgreater`/… library names**, which were previously unmodeled (havoced → unsound). Commit: "model isgreater/isless/isunordered…".
- **`__builtin_fabs/sqrt/floor/ceil/trunc/round/fmin/fmax/fmod`** (+`f`/`l` variants) — aliased to the library names `FpFunctionsToExprsPass` models. These return the first argument's type; since the `__builtin_` form has no declaration, the synthetic `CCall`'s return type is set explicitly (otherwise it defaults to int → ClassCastException against the fp result). Routing is allow-list-gated so unmodeled builtins still fail loudly rather than being silently havoced. Commit: "alias __builtin_ math functions…".

Still open in C3: `__builtin_alloca` (421, property-dependent — alloca→malloc is unsound for valid-memcleanup), `__builtin_va_*` (variadic, hard). And the `twoIntsStruct`/`example_user_t`/`node_t`/`u8` "No such variable" identifiers (~450) are entangled with function-pointer failures (C5) in the same files — not a standalone fix.

Not yet started (batch 2): C3 builtins, C1 east-const + GlobalDeclUsageVisitor hardening, N7 Newton MemoryAssignStmt, N6 pthread_detach, Phase 1.5 memsafety scope lifetimes, Phase 4 grammar, Phase 6 architectural. (**OC is now IN SCOPE as of 2026-07-16** — the external PR was merged into this branch; `&expr` remains a separate PR.)

### Batch 4 (post-re-test-3): function pointers, alloca, inline asm — IMPLEMENTED, awaiting full re-test

Three features, each verified not to disturb programs that don't use them.

**C5 function pointers — candidate-set dispatch** (commit `frontend: support function pointer calls via candidate-set dispatch`).
- A function's address is modelled as an **integer id** (`FunctionIds`, ids from `0x10000000`, never 0): above the data-pointer range, so a function id can never be confused with an object base or NULL. A function used as a value stays a `RefExpr` (this is what `CLibraryFunctionsPass` needs to resolve `pthread_create`'s start routine **by name**); the function's *variable* is initialised to its id via a global init.
- `FunctionPointerCallsPass` lowers an indirect call into **one parallel XCFA edge per candidate**, guarded by `Assume(fp == id_i)`, plus a fallback edge asserting no candidate matched and havocing the result. Candidates are the address-taken functions defined in the XCFA whose arity matches. Parallel edges — *not* a nested `NondetLabel`, which `splitIf` rejects and `InlineProceduresPass` cannot reach into.
- **Non-fptr programs are untouched**: the id globals are gated on `FunctionIds.hasIndirectCall()`, so a program that merely passes a function to `pthread_create` gains nothing. Verified by an A/B structural XCFA dump (`--enable-xcfa-serialization`) over all 31 `c2xcfa` fixtures, before vs after: **31/31 byte-identical**.
- Covers: plain fptr variables, typedef'd fptrs (incl. **global** typedefs — these go through `TypedefVisitor.visitGlobalDeclaration`, a *different* method from `visitDeclaration`), callback parameters, struct-field fptrs, `(*p->f)(x)` through a typedef'd struct pointer, void-returning fptrs, and **function-type parameters** (`void f(void g(int))`, which C decays to a pointer — handled in `visitOrdinaryParameterDeclaration`).
- ⚠️ The subtle bug to avoid: the direct/indirect test must be *"is the callee a function-pointer **variable**"*, **not** *"is it in the `functions` map"*. Library functions (`malloc`, `__VERIFIER_nondet_*`) are `RefExpr`s that are absent from `functions` because they are resolved by name much later — an early version routed them down the indirect path and broke 134 tasks.
- Result on a 225-task sample of the 1,543 previously-`Only variable-backed functions`-failing tasks: that error class is **eliminated (161 → 0)**; parse-OK 3 → 127.

**C3 `alloca`** (commit `xcfa: model alloca as a stack allocation excluded from the leak scan`). All 752 uses in sv-benchmarks are the undeclared `__builtin_alloca`, so the pointer return type is supplied explicitly on the synthetic call (it would otherwise default to int).
- The **memory-safety nuance**: pointer bases are partitioned by residue mod 3 — `3k+0` malloc'd heap, `3k+2` address-taken locals (`ReferenceElimination`) — and the memcleanup leak scan (`MemsafetyPass.annotateLost`) enumerates **only `3k+0`**. Memory from `alloca` is released automatically at function return, so reporting it as a leak would be a wrong result; `AllocaFunctionPass` therefore allocates it in the free residue class **`3k+1`**, sharing the `__malloc` counter so no two blocks alias. It still records a real size in `__theta_ptr_size`, so **out-of-bounds accesses to alloca memory are caught exactly as for the heap**. This reuses the convention stack locals already rely on rather than inventing one.
- Fixtures assert both directions: an alloca block is *not* reported as a leak, a genuine `malloc` leak *is* still caught in the same program (guards the residue split), and an OOB write into an alloca block is caught.
- Known gaps (both are the pre-existing W4 scope-lifetime limitation, not new): the block is never invalidated at function return, so a dangling access afterwards is missed, and `free()`ing it is accepted instead of being an invalid free.

**C7 inline assembly** (commit `frontend: model inline assembly (barriers as no-ops, outputs havoced)`). **No grammar change was needed** — the statement-level asm alternative already parses; it is the only alternative of `statement` beginning with a token rather than a sub-rule, so `visitStatement`'s `children.get(0).accept(this)` returned null and `CCompound.addCStatement` NPE'd. Detected and handled in the visitor.
- Semantics turn on the **template string**, and getting this wrong costs real results in both directions:
  - **Empty template** (`__asm__ __volatile__("" : "+r"(index))`, `("" : : : "memory")`) is not machine code but a **compiler barrier** — it leaves its operands untouched, so it is modelled exactly, as a **no-op**. Havocing here would be sound-but-imprecise and would inject **false alarms into aws-c-common**, where this idiom is pervasive (171+ occurrences).
  - **Non-empty template** (`__asm__("movq %%gs:%P1,%0" : "=r"(v) : …)`, thousands of occurrences in the Linux-kernel families) really executes and writes its outputs, so each **output operand is havoced** (sound over-approximation) and a warning is emitted that other side-effects are dropped.
- The 250+ glibc-header `__asm__("" "__isoc99_scanf")` declaration renames are a *different* grammar production (`gccDeclaratorExtension`) and already worked.
- The `CCompound` NPE class is **gone** (0/40 on sampled asm-bearing tasks). Those files now fail on *other*, unrelated causes — chiefly `__builtin_uaddl_overflow` (aws-c-common) and "Only structs expected here" (unions, AD7).

**Full-verdict sweep of the fptr tasks** (225-task sample, portfolio, 130 s — all 225 previously failed with `Only variable-backed functions`): **42 correct, 0 wrong**, 40 unknown/timeout (harness limits), 95 still ERROR. The 95 are *not* fptr failures — those files hit further, unrelated blockers (unions "Only structs expected here", `__builtin_*overflow`, `&expr`), so C5 unlocks them only partially. The number that matters: **0 wrong** — candidate-set dispatch introduced no unsound verdicts.

**Validation for batch 4** — canary suite (143 previously-correct tasks) re-run through the **portfolio**: **118 correct, 0 wrong, 0 errors** (the 25 unknowns are the local harness: 130–240 s timeouts, 4–8 JVMs in parallel, vs the benchmark's 15 min on dedicated cores — spot-checked serially and they solve). Module suites `:theta-c2xcfa:test :theta-xcfa:test :theta-xcfa-cli:test` green on `--rerun-tasks`. Harness lesson: drive canaries with `--backend PORTFOLIO` and use `canaries.tsv`'s `input_file_relpath` column — the `.yml` basename does **not** always match the source file.

### Batch 5: overflow builtins, unions — IMPLEMENTED, awaiting full re-test

**C3 `__builtin_*_overflow`** (commit `frontend: model unsigned overflow-checking builtins`). Every occurrence in sv-benchmarks is **unsigned** (`__builtin_uaddl_overflow` 348, `umull` 350, `uadd`/`umul` 8 each; 344 files, mostly aws-c-common) — there are no signed forms, which is what makes an exact model cheap: unsigned wraparound is *defined*, so both the result and the overflow condition can be stated in the operand type itself with no widening, and therefore work under **both** integer and bitvector arithmetic. Addition overflows exactly when the wrapped sum came out below an operand; multiplication exactly when dividing the wrapped product by one (nonzero) operand does not give the other back.
- The flag is captured into a temp **before** the result is stored, so the model stays correct when `res` aliases an operand (`__builtin_uaddl_overflow(x, y, &x)`). `FunctionVisitor.createTempVar` mints it, so it is registered like any local and reaches the XCFA.
- Fixtures pin the flag *and* the wrapped value in both directions, plus a non-vacuity control and a nondet input proving the flag is a real function of the operands rather than a havoc (`a + 0` never overflows, for every `a`).

**C8 unions** (commit `frontend: support unions (same-type members alias...)`). Previously a `union` definition silently degraded to `int` and any member access died with "Only structs expected here" (1,722 tasks).
- The enabling observation: a member access lowers to `__arrays_T[base][offset]` — **an array per SMT type**. So members of *different* types can never alias in this model regardless of offset, while members of the *same* type alias exactly when they share an offset. A union therefore reduces to **giving every member offset 0**; no bit-layout engine is required for the case that decides verdicts.
- That case is the dominant one: the **Juliet `_34` family** (whose stated theme is "a union with two ways of accessing the same data") puns between two members of *the same type* (`int64_t unionFirst` / `int64_t unionSecond`). Under offset-0 aliasing this is **exact** — a havoc-based model would have made the read nondet and flipped verdicts.
- Members with **different representations** (`union { char __size[4]; int __align; }`) cannot alias here, so an access to one is **rejected loudly** (`UnsupportedFrontendElementException`) rather than answered unsoundly. Such unions may still be *declared and passed around*, which is all the opaque system-header unions (`pthread_mutex_t`, `mbstate_t`) ever need — and that alone unlocks tasks that merely carry them.
- ⚠️ The guard compares **C types, not SMT types**: under integer arithmetic every integer type is the same unbounded `Int`, so an SMT-type comparison would let an `int` and a `char` member silently alias *without* the truncation C mandates (`u.i = 300; u.c` must be 44, not 300). An early version had exactly this hole; the fixture `un_trunc` pins it.
- Bit-exact punning across differently-typed members remains **AD7 future work** (the flat bitvector-object layout). Evidence that it is genuinely needed for the rest: 360 of 362 union definitions sampled contain an array member, so the "overlay scalars in one bitvector" shortcut does not generalise.

**Bug found and fixed while doing this**: `AllocaFunctionPass` kept its *own* companion map and so minted a **second, distinct `VarDecl` also named `__malloc`** instead of sharing `MallocFunctionPass`'s allocation counter — two same-named globals, and the counter's "initial creation" branch running twice. Commit `xcfa: share the allocation counter between malloc and alloca`.

### Batch 6: pointer-width type errors (LP64 / bitvector memory) — IMPLEMENTED

Investigating the `ClassCastException` above turned up **one bug class with four instances**, all pre-existing (reproduced at `ca8a0c4b8`, before any of this work) and all the same mistake: **a pointer-width value and an `int`-width value used interchangeably.** Under ILP32 a pointer and an `int` are both `Bv32`, so every one of these silently "worked"; under LP64 a pointer is `Bv64` against a 32-bit `int` and they throw. Under *integer* arithmetic every integer type is the same unbounded `Int`, so they were hidden there too. Net effect: **any pointer or array access was broken under LP64 + bitvector arithmetic**, and **memsafety was broken under bitvector arithmetic in _both_ data models**. LP64 is the *majority* data model in sv-benchmarks (35,573 tasks vs 15,040 ILP32), and bitvector arithmetic is forced by any bitwise operator — which is why this was such a large error cluster. Commit: `fix pointer-width type errors that broke LP64 and bitvector memory operations`.

1. **`ReferenceElimination`** built a dereference *offset* from `getSignedInt` while every other pointer site in the same file uses `getSignedLong` (pointer-width in both data models). `TypeUtils.cast` is a *checked* cast, not a conversion, so this threw on every dereference of an address-taken variable under LP64.
2. **`malloc`'s return type was not known to be a pointer**, so its call defaulted to `int`. Two ways to get there: a fixed-size array declaration is lowered to a *synthetic* `malloc` call the program never wrote; and — the interesting one — the ubiquitous glibc spelling **`void *malloc(size_t);`** *is not parsed as a function at all*. With an unnamed typedef'd parameter, the parser (which has no symbol table, and where `typedefName : Identifier`) can read `void *` `malloc` as **all specifiers**, leaving `(size_t)` to match a *parenthesized declarator* — yielding **two global variables**, `malloc` and `size_t`, and no function. Naming the parameter (`size_t n`) kills that alternative and the correct parse wins. This is the AD6 typedef-ambiguity, and it affects ~21k files. Rather than change the grammar, `FunctionVisitor` now records up front that `malloc` returns a pointer (a real declaration simply overwrites it with the same type). **The underlying grammar ambiguity remains and is still worth fixing under AD6** — this only neutralises its most damaging consequence.
3. **`StmtSimplifier`** (MemoryAssignStmt) bound `varDecl.getConstDecl(offset)` — a constant carrying the *pointer's* type — to the written value, which has the *element's* type. (Those const decls are the SSA-indexing mechanism `PathUtils` uses, not memory cells, so this constant-propagation is an optimization; where the types disagree it is now skipped.)
4. **`MemsafetyPass` / `PtrSize`** mixed the `__theta_ptr_size` array's *index* type (pointer) with its *value* type (`Fitsall`, `Bv129`): `allocate` cast the base to `Fitsall`, and two bounds checks compared a `Fitsall` size against a pointer-typed zero.

Effect on the union-bearing sample: **12/70 → 68/70 tasks now parse** (the 2 left are "Compound types are not directly supported"). A memsafety violation under bitvector arithmetic is now correctly reported (was a hard crash). All 15 feature fixtures and the canary suite stay green.

**Next blockers** (from a 300-task sample of frontend failures, after all of the above): `Overflow checking does not yet support bitwise arithmetic` (32 — the hard `check` in `OverflowDetectionPass`, Phase 5), `UnsupportedOperationException: We...` (12), and `ParseCancellationException` (9 — the grammar, Phase 4/AD6, still what blocks most of aws-c-common).

### Batch 7: bitvector arithmetic audit — IMPLEMENTED

Batch 6's bugs were all masked by ILP32/integer coincidences, so bitvector is where the rest hide. Running the **canary suite under forced `--arithmetic bitvector`** made that concrete: **70 of 143 canaries crashed**. Note this is not a synthetic configuration — the default `efficient` mode selects bitvector arithmetic for *any* program containing a bitwise operator, so these are live in the real benchmark. Commit: `fix bitvector-arithmetic bugs in pthread modelling and the memsafety size domain`.

**A wrong-result bug (the important one).** The memory model marks a freed object by writing **-1** as its size, and tests `size < 0` / `size > 0`. But sizes are `Fitsall`-typed and **`Fitsall` is unsigned**, so under bitvector arithmetic -1 is the *largest* representable value: `free()` never registers, and a program that correctly frees everything is still reported as **leaking**. Verified end-to-end with default settings (no flags): `malloc; p[0] = 1 & 3; free(p)` under `valid-memcleanup` takes the *violation* path at HEAD and is correctly `Safe` after the fix. `deallocate` now writes **0**, which means "not live" under signed *and* unsigned semantics, and coincides with the array's default value — so a never-allocated object is treated like a freed one, which is what the checks want anyway (the `free` check became `size <= 0`).

**`pthread_create`/`pthread_join` (26 canaries).** `CLibraryFunctionsPass` hardcoded the SMT integer literal `Int(0)` as their return value, which is a type error against the `Bv32` return variable under bitvector. The pass now takes a `ParseContext` and builds the zero from the variable's own C type.

**`Fitsall`'s casts contradicted its own type.** Its SMT type and literals are built as *unsigned* (`type instanceof Signed` is false), but `CastVisitor.visit(Fitsall)` routed through `handleSignedConversion`, so casting *to* Fitsall produced a **signed**-typed expression. Comparing that against anything genuinely unsigned unifies a signed with an unsigned bitvector, which yields a signedness-less (**neutral**) `BvType` — and `BvType.Leq` rejects those outright. Now `handleUnsignedConversion`, consistent with the type. ⚠️ Making `Fitsall` *signed* instead is the wrong fix and was tried and reverted: it is a shared type feeding promotions, and changing its identity regressed the integer memsafety path.

Result: forced-bitvector canary crashes **70 → 44**, and the remaining 44 are all *known feature gaps*, not type bugs: 38 are the deliberate `check` in `OverflowDetectionPass` (Phase 5), the rest "Pointer arithmetic not supported" / "Compound types are not directly supported". Canary suite (default arithmetic, portfolio): **143/143 correct, 0 wrong, 0 errors** (was 118 correct).

**One bug found but NOT fixed**: **`Neutral BvType` on `&local` + memsafety + bitvector** (`ref_ms` fixture, `memsafety-ext3/scopes2.c`). Every comparison in `MemsafetyPass.annotateDeref` was verified signedness-consistent after the cast fix, so the offending `BvType.Leq` is at some *other* site not yet located. It is the last remaining forced-bitvector canary crash.

---

## IMPLEMENTATION STATUS — batch 8 (solver model extraction, bitvector overflow checking)

### Z3 model extraction of array sorts — FIXED
`Z3TermTransformer.transformSort` handled Bool/Int/Real/BitVec and threw `AssertionError: Unsupported sort` on anything else. Arrays **nest** — the memory model is `__arrays_T[base][offset]`, an array of arrays — so the element sort handed to it is itself an array, and it threw on *every* counterexample whose model touched memory. Since `__theta_ptr_size` and `__arrays_*` are arrays, that is the normal case for memsafety: genuine **Unsafe** verdicts were being turned into **ERROR**s in both arithmetics. Added the recursive `ArraySort` case (and `FPSort`, equally missing). Commit: `solver-z3: transform array and FP sorts when extracting models`.
- All 10 memsafety fixtures (leak / use-after-free / out-of-bounds / double-free / clean-free) now give correct verdicts under **both** arithmetics; previously the four Unsafe ones errored out.

### Overflow checking under bitvector arithmetic — IMPLEMENTED (Phase 5)
`OverflowDetectionPass` began with `check(arithmetic != bitvector)`, so **3,658 no-overflow tasks** errored outright. The reason it was hard: under integer arithmetic the operation is carried out in the unbounded integers, so overflow is caught by range-checking the *result* against the C type's limits — but a bitvector operation has **already wrapped**, so its result is trivially in range, and the bitvector `LimitVisitor` was accordingly just `Assume(true)`.

**Investigation of the SMT side**: there is **no overflow flag** in SMT-LIB. Z3 does expose `bvadd_no_overflow`/`bvmul_no_overflow`/… (`Z3_mk_bvadd_no_overflow`), but they are **non-standard**, so using them would tie overflow checking to Z3 and require new core expression kinds plus transformers for every solver. The portable encoding — and the one implemented, in `BvOverflow.kt` — is **widening**: redo the operation in a wider bitvector and check the narrow result still agrees.
- `a + b` overflows exactly when `SExt(a +ᵥᵥ b, w+1) != SExt(a, w+1) + SExt(b, w+1)`. One extra bit suffices for `+`/`-`; a product needs `2w`.
- Negation and division cannot be caught by widening (each overflows on exactly one input), so they are stated directly: `-x` overflows iff `x == INT_MIN`; `x / y` iff `x == INT_MIN && y == -1`.
- C evaluates `a + b + c` as `(a + b) + c` and **either step can overflow on its own**, so an n-ary operation is folded left-to-right and each step checked against the *wrapped* running value, exactly as the program computes it.
- Uses only `SExt`/`Eq`/the existing arithmetic — no new core ops, works on any BV solver.

**`abs` is now modelled** (`abs`/`labs`/`llabs`/`imaxabs` → `x < 0 ? -x : x`). This was not optional: leaving it havoced makes a guard *written in terms of it* (`if (abs(x) < K)`) constrain nothing, which surfaced as a **false overflow report on `_good` (no-overflow) Juliet tasks** — code that is careful *precisely because* it uses `abs` to bound its input. It was the single WRONG result in the no-overflow sample. `abs(INT_MIN)` correctly remains an overflow (the negation it expands to is exactly the `NegExpr` case).

**A bug in batch 4's own function-pointer code, found here**: the function-id literal was built as a *signed int*, but the id-holding variable's type follows the function's **return** type — a `long`-returning function gets a 64-bit variable, and a 32-bit literal is a type error. Same "widths coincide under integer/ILP32" pathology as batch 6. Now built from the variable's own type.

**Validation**: forced-bitvector canary crashes **70 → 44 → 6** (the 6 are the `Neutral BvType` case plus known feature gaps — "Pointer arithmetic not supported", "Compound types are not directly supported"). On a 60-task sample of the no-overflow tasks that previously errored on the guard: **23 correct, 0 wrong** (was 22 correct / 1 wrong before the `abs` fix). Overflow fixtures pin all four overflow kinds *and* the near-miss (`INT_MAX - 647 + 1`, which must **not** be a false alarm) under both arithmetics; the integer path is unchanged. All 26 feature fixtures green; all module suites green.

---

## IMPLEMENTATION STATUS — batch 9 (neutral BvType, void-typed casts)

Commit: `keep bitvector signedness through constant folding; handle void-typed casts`. Closes the last two forced-bitvector crash classes.

### `Neutral BvType cannot be used here` — FIXED (a core bug, not a memsafety one)
A `BvType` carries a **nullable** signedness, and `BvType.Lt/Leq/Gt/Geq` reject a "neutral" (signedness-less) one outright. The bug: **constant folding threw the signedness away.** `ExprSimplifier.simplifyBvAdd` (and its 13 siblings) seed their accumulator with `Bv(new boolean[size])` — a *neutral* zero — and every `BvLitExpr` arithmetic method returned `bigIntegerToNeutralBvLitExpr(...)`. So the expression *tree* carried proper types, but the moment a value was constant-folded the result became neutral, and any later comparison against it threw. `TypeUtils.getDefaultValue` did the same for every uninitialised bitvector variable.
- Fix: `BvLitExpr` operations now keep the operand's signedness (`zext`/`sext` take the *requested* type's), the folding accumulators are seeded with `expr.getType().getSignedness()`, and `getDefaultValue` builds the literal in the type it was asked for. New `BvType.getSignedness()` exposes the nullable field — ⚠️ the existing `getSigned()` returns a **primitive** `boolean` and silently collapses `null` → `false`, which is why probing signedness through it is misleading (it cost me an hour).
- Symptom was `&local` + memsafety + bitvector: `ReferenceElimination`'s stack-pointer base got constant-folded into a neutral literal. `memsafety-ext3/scopes2.c` now reports the correct **Unsafe**.

### "Compound types are not directly supported!" — FIXED (two distinct bugs)
1. **`(void)e` corrupted the operand's type.** `visitCastExpressionCast` did `castTo` — which for `CVoid` is the *identity* — and then stamped `cType = void` on the result. Since a variable's `RefExpr` is a single shared instance, `(void)x` made **x look void everywhere it was used**, breaking every later conversion of it. Now a void cast returns the operand untouched.
2. **A void-typed *source* threw.** Reached through the standard assert expansion `cond ? (void)0 : fail()`, whose arms are both void so the frontend unifies them to a common type. A void expression has no value and C forbids reading one, so the bitvector `CastVisitor` now yields the target's zero. (Under integer arithmetic this never surfaced: there the conversion ignores the source type entirely.)

**Validation**: forced-bitvector canary crashes **6 → 2** — and the last 2 are `loops/array-{1,2}.c` hitting *"Pointer arithmetic not supported"*, a genuinely unimplemented feature rather than a type bug. Canary suite (default arithmetic): **143/143 correct, 0 wrong, 0 errors**. All 28 fixtures green. Core/solver/xcfa suites green (`:theta-solver-smtlib:GenericSmtLibHornSolverTest` fails identically at HEAD — a missing solver binary in this environment, not a regression).

---

## IMPLEMENTATION STATUS — batch 10 (division overflow, typedef-aware parsing)

### N3 division overflow — FIXED (Phase 5.1 complete)
`OverflowDetectionPass` refused to check *any* program containing a division (`throw UnsupportedOperationException("We cannot soundly detect overflows with divisions.")`), which is why "division 831" was its own error cluster. The reason it could not simply range-check the result: C's `/` lowers to the solver's `div`, which is **unconstrained when the divisor is zero** — so the "result" could be any value, and a range check on it would report an overflow for a program that merely divides by zero (a different undefined behaviour, and not this property's concern). Division overflows on exactly one input pair, so that is now stated directly: `INT_MIN / -1`, whose true result is one past the maximum. The bitvector path already had this in `BvOverflow.kt`; the integer path needed the same condition plus a `cType` on the `Div` buried inside `createIntDiv`'s rounding-adjustment `Ite`. Commit: `detect division overflow (INT_MIN / -1) instead of refusing to check programs with divisions`.
- Fixtures pin `INT_MIN / -1` (Unsafe), ordinary division (Safe), **division by zero (Safe — not an overflow, the false-alarm risk)** and negative-operand rounding (Safe), under both arithmetics.
- On the 60-task no-overflow sample: errors **26 → 11**, correct 23 → 26, still **0 wrong**.
- ⚠️ Still unchecked in both modes: **signed shift overflow** (`E1 << E2` past the type's range). Deliberately not added yet — it risks false alarms on code that shifts signed values, and wants its own measured pass.

### Phase 4 / AD6 — typedef-aware parsing — IMPLEMENTED
The grammar could not tell a type name from any other identifier (`typedefName : Identifier`), which is what made `(a) * b` ambiguous and what made **`void *malloc(size_t);` parse as two *variables*** rather than a function. C resolves this with a symbol table, so the parser is given one. Commit: `parse C with a typedef symbol table, so type names and identifiers are told apart`.
- **Two passes**: a first, error-tolerant parse (behaving exactly as before — every identifier may be a type) harvests the file's typedef names straight off the parse tree; the real parse then accepts only those as types. If the type-aware parse fails, it **falls back to the old permissive one**, so nothing that parses today can start failing.
- ⚠️ **The predicate has to sit on the cast alternative, not only inside `typedefName`.** ANTLR only uses a predicate to *choose* an alternative if it can reach it **without consuming a token**, and the one in `typedefName` lies past the `(`. Left there alone, prediction assumes it true, commits to the cast, and only then evaluates it — turning `(a) * b` from a mis-parse into a hard **parse error**. `castExpression` therefore carries `{startsCast()}?`, which looks at the token after the `(`. (`sizeof` needs nothing: it already decides *after* consuming its `(`, so the token it tests is the right one.)
- The collection pass must **not** run the frontend's own visitors: they have side effects (registering struct tags, writing `cType` metadata into the shared `ParseContext`), and running them twice over a file corrupts the real parse. Names are read off the tree directly.
- **Validation (the "handle with care" protocol)**: XCFA **byte-identical on 31/31** `c2xcfa` fixtures (no silent reinterpretation); canary parse sweep **143/143 OK** (zero new parse failures); canary verdicts **143/143 correct, 0 wrong, 0 errors**; a new **15-test ambiguity suite** in the parsing submodule (`CTypeNameAmbiguityTest`) asserting *parse-tree shape* — cast vs multiplication, `(f)(1)` as a call, comma expressions, `sizeof(type)` vs `sizeof(expr)`, the malloc declaration, and the permissive fallback.
- **Effect**: on a 120-task sample of the tasks that failed the frontend in `results-0711`, **116 now parse** (it was 39/300 before). This collapses the `ParseCancellation` cluster *and* the whole downstream cascade of the malloc mis-parse at once.

### ⚠️ NEW WRONG-RESULT BUG FOUND (top of the queue): `&&` / `||` do not short-circuit function calls
The verdict sweep over the newly-parsing tasks surfaced **8 wrong results**, all one family (`CWE190_Integer_Overflow__int64_t_rand_square_*_good`, reported *false* on no-overflow when the answer is *true*). It is **not** the parse. The guard is

```c
if (data > (-0x7fffffffffffffff - 1) && imaxabs((intmax_t)data) <= sqrtl(...))
```

and C guarantees `imaxabs` is called **only when the left conjunct holds**. Theta evaluates the operands of `&&` by visiting each in turn and letting their side effects (here, the call) land in `preStatements`, which are emitted **before** the condition — so `imaxabs(INT64_MIN)` *is* executed, its negation genuinely overflows, and a program that is careful precisely because it guards against `INT64_MIN` gets reported as overflowing. Reduced to a fixture (`data > INT64_MIN && imaxabs(data) <= K` → Unsafe, must be Safe); no floating point involved.
- **FIXED** (commit `evaluate the operands of && and || under their short-circuit`): `visitLogicalAndExpression` / `visitLogicalOrExpression` now lift the statements an operand added back out of `preStatements` and re-emit them inside a `CIf` on the operands already evaluated — all of them holding, for `&&`; none of them, for `||`. Fixtures pin all three directions: the call must *not* run (`x != 0 && f()` with `x == 0`), must *not* run (`x != 0 || f()` with `x != 0`), and *must* run (`x != 0 && f()` with `x != 0`). Canary suite 143/143, 0 wrong.
- ⚠️ Two things worth knowing for the next person: the builder insists an `if`'s guard be a `CCompound` **with its pre/post-statement slots filled** (otherwise it takes a path that demands the compound's last statement be a compound too, and throws "Currently only CCompounds have pre- and post statements!"). And *expressions* never needed this: `OverflowDetectionPass.getExpressions` already threads a short-circuit condition through `AndExpr`/`OrExpr` and wraps a guarded expression as `Ite(cond, expr, 0)`, and `MemsafetyPass` has `derefsWithShortCircuitCond`. It is only the statements a call is lifted into that escaped the guard.

### RESOLVED: the abs-style bound false alarm — havoced values were not values of their C type
The 8 `int64_t_rand_square_*_good` false alarms are **fixed** (commit `constrain havoced values to the range their C type can hold`). The cause was not abs, not the short-circuit, and not the nonlinearity: **a havoc is unbounded, and under integer arithmetic that is not the same as a C value.** A nondet `long long` became an arbitrary *mathematical* integer, with nothing saying it is at most `LLONG_MAX`. Code that bounds such a value from one side only —

```c
if (a > -3037000500 && llabs(a) <= 3037000499) { r = a * a; }
```

— is then not bounded at all, and the analysis "finds" an overflow at a value no C program could ever have produced. (The linear form `a <= K && a >= -K` bounds both sides itself, which is exactly why it verified while the abs form did not.)
- The `LimitVisitor` — the thing that says a value of type `T` is representable in `T` — existed but was used **only** by `OverflowDetectionPass`. Nothing applied it to havocs. `NondetFunctionPass` and `UnresolvedInvokeToHavocPass` now follow each havoc with that range assume (`TypeRange.kt`), and only when the C type is actually **known** — without the metadata, `getType` guesses from the SMT type, and a guess is no basis for constraining a value.
- Under bitvector arithmetic the width already does this, so the limit visitor yields `true` there and the change costs nothing.
- All 8 tasks now report the correct **Safe**, every `_bad` twin is **still caught**, and every overflow fixture (add/sub/mul/neg/div, the near-misses, division-by-zero) is unchanged. Canary suite 143/143, 0 wrong, 0 errors; module suites green.
- ⚠️ Diagnosis note for the next person: I first "reproduced" this at ILP32 while the task's `data_model` is **LP64**, which made `int64_t` (via glibc's `typedef signed long int __int64_t`) a *32-bit* variable and produced a completely different, spurious explanation. **Always take the data model from the task's `.yml`.**
- ⚠️ The first cut of this fix **broke 14 tasks** (4 correct → error): the *integer* `LimitVisitor` has **no catch-all**, so asking it for the range of a type that has none (a pointer, a struct) hits the base visitor's "Not (yet) implemented" throw. `withinTypeRange` now leaves such a type unconstrained, as before. Caught by re-measuring the no-overflow sample — the canary suite did not surface it, because no canary havocs a pointer-typed value.

### Signed shift-left overflow — IMPLEMENTED (Phase 5 complete)
`a << b` is `a * 2^b`, so it overflows when that product no longer fits. Same widening encoding as the rest (`BvOverflow.kt`): redo the shift in twice the width and require the narrow result to still agree. Shifts force bitvector arithmetic (they are bitwise), so there is no integer-mode counterpart to write. Commit: `detect signed shift-left overflow; do not range-constrain types without a range`.
- **Deliberately does not flag a negative left operand.** C calls `-1 << k` undefined, but flagging it would condemn an idiom that appears throughout real code and would have produced false alarms; only the *value* is checked. Fixtures pin all four cases: `1 << 31` on `int` overflows, `1 << 30` does not, an **unsigned** shift never does, and `-1 << k` is not flagged.
- Measured before keeping it, since the false-alarm risk was the whole question: on the 60-task no-overflow sample, **26 correct / 0 wrong / 11 errors** — identical to the pre-shift baseline, so shift checking added no false alarms and no new errors. Canary suite 143/143, 0 wrong, 0 errors.

### (historical) the investigation that led there
The 8 `int64_t_rand_square_*_good` tasks are **still wrong** after the short-circuit fix, for an unrelated and **pre-existing** reason. Reduced, with no call and no floating point:

```c
if (a > -3037000500LL && (a < 0 ? -a : a) <= 3037000499LL) { long long r = a * a; }   // reports Unsafe; is Safe
if (a <= 3037000499LL && a >= -3037000499LL)               { long long r = a * a; }   // correctly Safe
```

Two *linear* bounds prove `a * a` in range; the same bound expressed through the abs idiom (`Ite(a < 0, -a, a) <= K`) does not, and the analysis reports an overflow. It is not the nonlinearity (the linear-bound version proves it), not the short-circuit, and not `imaxabs` (the ternary reproduces it without any call — and `abs` is modelled as exactly this `Ite`). Next step: dump the counterexample and see which `a` it claims, and whether the reported overflow is on `a * a` or on the `-a` inside the `Ite` (whose short-circuit wrapper may not be doing what it looks like it does).

## IMPLEMENTATION STATUS — batch 11 (the GCC extensions that blocked whole families)

With the typedef ambiguity gone, `ParseCancellationException` was *still* the top error (≈87 of 202 in a 298-task sample). Reading the offending tokens rather than guessing showed why: a handful of GCC extensions the grammar simply did not know, each sitting in a glibc header line that no task actually uses.

- **`__builtin_va_list`** — **9,269 files**. Present only as `typedef __builtin_va_list __gnuc_va_list;`. A variadic argument list is opaque (a program may only hand it to `va_start`/`va_arg`/`va_end`), so a pointer-wide stand-in is enough for that line to go through.
- **`__inline`** — **15,677 files**. The grammar knew `__inline__` but not `__inline`. Likewise `__const`, `__restrict__`, `__signed__`.
- **`restrict`** was worse than unknown: it **threw** (`"Not yet implemented 'restrict'!"`). It is a *promise* that an object is not reached through another pointer — a licence to optimize, saying nothing about the values a program computes. Not exploiting it is sound; refusing the program over it is not. Now accepted and ignored, in every spelling (12,819 files use `__restrict`).
- **`__attribute__` after `struct`/`union`** (`typedef union __attribute__((__transparent_union__)) {...}`) — 16 of 50 sampled parse failures. Attributes describe *layout*, which is not modelled, so they are matched and ignored as everywhere else.
- **`__builtin_va_arg(ap, T)`** — takes a *type* as an argument, which the expression grammar could not parse (the rule was in `C.g4`, commented out). Enabled, and modelled as a fresh nondeterministic value of the requested type: the argument list is not built, so that is the only sound thing to say about what reading from it yields.
- **`sizeof *p`** — `sizeof` without parentheses.
- **Variadic functions dropped their *named* parameters.** `DeclarationVisitor` bailed out on seeing `...` and added none of them, so `n` in `int sum(int n, ...)` was undeclared inside the function's own body. Only the variadic *tail* is unmodelled.

Commits: `parse the GCC extensions that blocked whole benchmark families`, `accept restrict and the GCC qualifier spellings instead of refusing the program`.

**Validation** (the "handle with care" protocol): XCFA **byte-identical 31/31** on both commits, canary parse sweep **143/143 OK**, canary verdicts **143/143 correct, 0 wrong, 0 errors**, module suites green.

⚠️ **Caught myself introducing a latent bug**: adding `__const`/`__restrict__` to the *grammar* without adding them to `visitTypeQualifier`'s switch, which throws on anything it does not recognise. The fixture only passed because the declaration using them was unused and got pruned. **A grammar keyword needs a visitor case, and the fixture must actually *use* the declaration.**

### C1 east-const — FIXED, by rewriting `mergeCTypes` (test-driven)
Commit: `pick a declaration's type by what its specifiers are, not by their order`.

**The bug.** A declaration's specifiers arrive as a *list*, in whatever order they were written, and C attaches no meaning to that order: `unsigned long int` = `long unsigned int`, and `const T` = `T const`. `mergeCTypes` picked the **last** named specifier as the type (its own comment: *"if typedef, then last element is the associated name"*). And `visitTypeSpecifierPointer` returns a **nameless** `NamedType("")` when it matches a bare `*` with no type before it. Put together:

| declaration | specifiers | main type chosen |
|---|---|---|
| `const struct S *p` ✓ | `[]` | `Struct/ptr1` — `struct S *` is adjacent, so the pointer rule swallows the struct and returns *it* |
| `struct S const *p` ✗ | `[Struct/ptr0]` | **`NamedType('')/ptr1`** — the `const` breaks that adjacency, the bare `*` yields the nameless type, and *it* is last |

So the struct was demoted to a mere modifier and `p` came out a `void *` — whereupon `p->field` said **"Only structs expected here"**. It went unnoticed for the west-const spelling precisely because the pointer is absorbed there.

**The fix.** The namer is now chosen by *what a specifier is*, never by where it sits: a specifier names a type unless it is nameless (a bare `*`, which carries only a pointer level) or a width word (`long`/`short`/`unsigned`/`_Bool`/`__int128`, which only say how wide an `int` is). With no namer at all, the type is the `int` that was never written down. This also retires the old "shorthand" special case — `int long x` and `long int x` now come out the same way for the same reason.

**Test-driven, as it had to be.** A new **60-case suite** (`CTypeDeclarationTest`) parses real declarations and asserts the resulting `CComplexType`, *written before the fix*: the plain types, specifier-order permutations (`int unsigned long`), qualifiers in both positions, pointers, structs, and typedef'd structs and scalars. It caught exactly the 5 east-qualifier cases and nothing else, and all 60 pass after.
- The harness initially parsed *permissively*, which made it take the variable's own name `x` for a type — a misleading picture. Fixing that meant moving the two-pass type-aware parse out of `c2xcfa` into the frontend (`CParseUtils.kt`), where the parser lives; the test and the pipeline now go through the same entry point. **A parser test that does not use the real parse path is worse than no test.**
- Validation: XCFA **byte-identical 31/31**, canary parse 143/143, canary verdicts **143/143 correct, 0 wrong, 0 errors**, all module suites green. On the 298-task sample: PARSE_OK **96 → 103**, and the `IllegalStateException` cluster (which held "Only structs expected here") **78 → 59**.

### (historical) C1 east-const — how it was located
25 of 70 sampled downstream failures are `Only structs expected here`, and it is **not** unions. It is **east-const**:

```c
static void show(S const *p) { p->a; }        // "Only structs expected here"
static void show(const S *p) { p->a; }        // fine
```

It fails for `struct _S const` just as for the typedef'd `S const`, so it is the trailing qualifier, not the typedef. The suspect is `TypeVisitor.mergeCTypes`, which picks the **last** named element as the type — its own comment says *"if typedef, then last element is the associated name"* — an assumption east-const breaks. ⚠️ But a probe showed `mergeCTypes` is **not reached with the struct at all** for the failing declaration, so the type is being built somewhere else; find that path before changing `mergeCTypes`. (`const` itself maps to `null` in `visitTypeQualifier`, so it cannot be the stray element on its own.)

## IMPLEMENTATION STATUS — batch 12 (the cost of the two-pass parse, and a bug it hid)

Prompted by the question *"does parsing twice cost us anything — do we re-parse the typedefs for every type?"*. Measured rather than guessed, by timing both passes across the 143 canaries.

**No, and no.** `parseTypeAware` has exactly **one** production call site (`getXcfaFromC`), reached **once per program**; moving it from `c2xcfa` into the frontend was a pure relocation. Nothing is re-parsed per type — the typedef names are collected once into a set the parser then consults in O(1).

The two passes are *not* symmetric, and in the useful direction:

| pass | mean | why |
|---|---|---|
| collect (permissive) | **438 ms** | every identifier may be a type name, so the grammar is genuinely ambiguous and ALL(*) has to work for its answer |
| strict (type-aware) | **57 ms** | knowing the type names removes the ambiguity — **~8× cheaper** |

So the added cost is the *strict* pass, not a doubling: **6,915 ms → 7,984 ms** over 12 canaries, ≈ **+89 ms/file**, ~15% of frontend wall time *including JVM startup* — against a 900 s task budget, noise.

⚠️ **The measurement found a real bug.** 27 of 143 canaries (**19%**) were paying for a **third** parse: the strict parse threw and silently fell back to the old permissive one. Cause: the collector's `lastIdentifier()` took the **attribute's** name for the type name in
`typedef struct {...} __pthread_unwind_buf_t __attribute__ ((__aligned__));` → `__aligned__`. The real name was never collected, so every later use of it failed to parse. Fixed with `lastTypeName()` (searches for a `TypedefNameContext`); **fallback rate 27/143 → 0/143**. Those 19% of files had been quietly getting the old buggy tree — none of the typedef work reached them.

An **SLL prediction fast path** was tried for the collect pass and **removed again**: measured 1,629 ms vs 1,585 ms for plain LL over the same files, i.e. no gain (the cost is not full-context resolution), and SLL can silently pick a different parse than LL on an ambiguity. Not worth the code.

*Optional future optimization, not taken:* a single-pass parse that registers each typedef name as its declaration is reduced would drop the collect pass entirely and be **faster than the original one-pass parser ever was** (57 ms vs 438 ms), since it would never parse ambiguously. It is delicate — ANTLR runs actions only when not speculating, so a lookahead crossing a typedef declaration would predict against an incomplete symbol table — and at +89 ms/file the payoff does not justify the risk today.

Commit: `collect a typedef's name, not its attribute's`.
**Validation**: module suites green, canary verdicts **143/143 correct, 0 wrong, 0 errors**.

## IMPLEMENTATION STATUS — batch 13 (`a[j]` silently retyped `j` to an array)

"Pointer arithmetic not supported" (**65 tasks**) turned out not to be about pointer arithmetic at all. `loops/array-1.c` has none — it is `for (j = 0; j < SIZE; j++) a[j] = ...`, the most ordinary loop in C. Printing what the guard was actually looking at ended the guessing at once:

```
lval=main::j  lvalType=...compound.CArray   ← the loop counter, "an array"
rexpr=(bvadd main::j #b0…01)
```

**A C type is recorded per expression, in a map keyed by the expression** (in fact by its *hash code*, `FrontendMetadata`). A cast between two types of equal width and signedness is a no-op, so `CastVisitor` **hands back the very expression it was given** — and `CComplexType.castTo` then records the target type on it. When the returned expression *is* a variable's `RefExpr`, that rewrites **that variable's type everywhere it occurs**.

`ExpressionVisitor.dereference` cast the *index* to the **pointer's own C type** (`ptrType.castTo(offset)`). `CArray`/`CPointer` are `CInteger`s of pointer width, so for an `unsigned` index under ILP32 the cast is a no-op — and `a[j]` recorded **`j` itself as an array**. Every later `j++` then read as pointer arithmetic and the whole program was refused. Invisible under integer arithmetic (that conversion always builds a new expression, so it has nothing to alias), which is why it presented as a "forced-bitvector" crash class.

**The fix**: an offset is an *index*, so it is cast to the index type — the same `unsigned long` the zero-offset default and the initializer-list dereferences already use, and pointer-wide in every data model. One line.

Genuine pointer arithmetic (`int *p = a + 1;`) is **still** refused, and correctly: a pointer *value* is an object id, memory is `arrays[base][offset]`, so `p = q + 1` would give `p` an id of its own, naming a different object entirely. The message now says which assignment.

Result: `loops/array-1.c` → **Safe** ✓ and `loops/array-2.c` → **Unsafe** ✓ (both previously errored out); every reduction of the loop shape builds under both arithmetics.

⚠️ **The root hazard remains and is worth knowing about**: *any* no-op `castTo` aliases its operand and rewrites its recorded type. It is harmless between integer types of equal width and signedness (they behave identically), but it is **not** harmless for compound types, and `(char *)q` on an `int *q` still silently retypes `q`'s own elements. This is the third bug of this shape (after `(void)e` in batch 9). The real fix is for `castTo` to refuse to stamp a type onto an expression it did not create — deferred, because it changes every cast in the frontend and wants its own validation round.

Commit: `an array index is an index, not a pointer`. New `ArrayIndexTypeTest` (4 cases × both arithmetics) pins that indexing leaves the index's type alone.

## IMPLEMENTATION STATUS — batch 14 (the archive shipped non-executable solvers)

Chasing a phantom: the canary suite came back **118/143** twice, the 25 losses all float/bitvector tasks, reproducibly, on an idle machine. Not a regression — **`Zip` does not carry a source file's mode across**, so the solver binaries installed at `-rwxr--r--` went into the archive as `-rw-r--r--`. cvc5 and mathsat could not be executed, the portfolio configurations that use them died on startup (`GenericSmtLibSolverBinary.<init>` → `IllegalStateException`), and exactly the tasks needing those configurations returned **no verdict at all**.

This was never merely a local-harness annoyance: **the archives we ship to SV-COMP had unusable solvers**, in all four variants (`Theta-svcomp`, `EmergenTheta-svcomp`, `Thorn-svcomp`, `Theta-chccomp`). `theta-start.sh` and the smoketest already carried explicit `filePermissions { unix(0755) }` lines — evidence the same trap had been hit before and patched per-file rather than at its cause. The solvers copy spec had no such line.

Fixed in the shared plugin (`buildSrc/.../archive-packaging.gradle.kts`) by *preserving* the source's bit rather than blanket-chmod'ing:

```kotlin
eachFile { if (file.canExecute()) permissions { unix(0b111101101) } } // 0755
```

Verified: `cvc5`, both `mathsat`s, and Thorn's `eld`/`golem`/`z3`/`yices` launchers are `rwxr-xr-x` in the zip, while `COPYING`, headers and eldarica's 0644 `convert.sh` are untouched. The dist now runs **straight out of `unzip`, with no `chmod`** — canaries **142/143**, the one outlier being `loop-industry-pattern/mod3.c.v+sep-reducer.c`, which needs more than the harness's 240 s and answers Safe correctly at the real 900 s budget (identical on HEAD).

Commit: `keep the solver binaries executable in the archive`.

⚠️ **The reason this hid for two full sweeps**: the sweep script bucketed *crashes* and *timeouts* together as one `UNKNOWN_OR_TO`. A broken harness then looks exactly like a verdict regression. Keep them apart (`verdict4.sh` now does).

## IMPLEMENTATION STATUS — batch 15 (the root of the retyping bug: a no-op cast must not alias)

Batch 13 fixed the *symptom* (`a[j]` retyping `j`); this fixes the cause, and the fix was suggested in one line: **"no-op casting usually wraps the operand in a `Pos()` — couldn't we just do that?"** It could, and the frontend was already half doing it.

`CComplexType.castTo` records the target C type on whatever the cast visitor hands back, and types are keyed by the expression itself. So a cast visitor that returns its operand *unchanged* rewrites that operand's own type. The **integer** cast visitor never had this problem because it already returns `Pos(param)` for the identity case — a fresh wrapper with its own identity, which is exactly why the bug was invisible under integer arithmetic. The **bitvector** one returned the bare operand:

```java
} else { // widths equal, signedness equal
    return Pos(param);   // was: return param;
}
```

Two lines, both the equal-width/equal-signedness branch. This is not a new mechanism — it makes bitvectors do what integers have always done — and it retires the whole bug class, not just the array-index symptom (`(char *)q` on an `int *q` no longer retypes `q`'s elements either).

**Verified as the root fix**: with the batch-13 `dereference()` change backed out, `ArrayIndexTypeTest` passes on the `Pos` change alone (all 4 cases). Both are kept — typing an index as an index is independently right.

⚠️ **It exposed a latent bug in the C printer.** `XcfaToC` round-tripping (XCFA → `xcfa.c` → re-parse) broke on `03bitwise.c`: `IntPosExpr`'s operator label is `"+"`, but `BvPosExpr`'s is `"bvpos"`, so the printer emitted `(bvpos x)` — not C. The gap was always there; nothing had ever produced a `BvPos` before. `PosExpr` now maps to unary `+` whatever the type.

**Validation.** A `Pos` is *invisible to the solver* (`transformBvPos` → `toTerm(op)`, so the SMT term is unchanged), but that had to be shown at runtime rather than argued: an A/B of the 60-task no-overflow sample against two dists differing only in this change puts **every single task in exactly the same bucket** (19 CORRECT / 11 ERROR / 30 UNKNOWN, both). Canaries 142/143 (the one outlier being the known-slow `mod3.c.v+sep-reducer.c`), all module suites green.

Commit: `a no-op bitvector cast gets its own expression to be typed`.

## IMPLEMENTATION STATUS — batch 16 (three function-pointer bugs, each hiding the next)

Chasing the `ClassCastException` cluster in the no-overflow sample. Three of the eleven errors were `ClassCastException`, all in Juliet's `_44`/`_65` variants -- "data flow through a function pointer". Fixing the crash exposed a second bug; fixing *that* exposed a third, which was the worst of the three.

### 1. The crash: an inlined call's result written at the callee's type
`InlineProceduresPass` converts *arguments* properly (`castTo`), but the **out** direction -- writing the callee's result back -- built the assignment at `param.first.type`, the **callee's** type, though its destination is the **caller's** variable. Indistinguishable whenever the two agree, and they nearly always do. But a call through a function pointer has no signature to go by, so the frontend types its result an `int` while the callee may return anything: for a `void` callee this asked to cast a 32-bit variable to the 1-bit placeholder, and threw. The assignment is now built at `varDecl.type`, which is what it writes into.

### 2. A function's address, truncated
`FunctionIds` numbers functions from `0x10000000` -- **29 bits** -- but the id was stored in the function's designator variable, which was typed by the function's **return type**. Anything narrower silently truncated it to 0, so the dispatch guard `fp == id(f)` could never hold, the branch was infeasible, and **the callee was never explored**. Same program, changing only the return type:

| `sink` returns | id variable | verdict on a program that *does* overflow |
|---|---|---|
| `long` / `int` | 64/32-bit | Unsafe ✓ |
| `short` | 16-bit | **Safe** ✗ |
| `char` | 8-bit | **Safe** ✗ |
| `void` / `_Bool` | 1-bit | **Safe** ✗ |

A program reported *safe* on the strength of a call that had been quietly dropped -- and callbacks are usually `void`. The designator is now typed as what it is: an address, pointer-wide.

### 3. A function's address, never initialised  ⚠️ the worst one
Fixing (2) produced a **false alarm** on `CWE191_..._65_good`, which is why (2) alone was not committed. A C file normally **prototypes** a function before defining it. The variable standing for its address belongs to *that* declaration, so at the definition `createVars` was skipped -- and the definition's `funcDecl.getVarDecls()` came back **empty**. That empty list is exactly what `FrontendXcfaBuilder` walks to create the id global. No global, no initial value: **the function pointer held an arbitrary value**, every candidate's guard became satisfiable, and a call could land in *any* function of the right arity. In the Juliet task, `goodB2G`'s random input was dispatched into `goodG2B`'s **unchecked** sink and reported as an underflow the program can never reach.

It cuts both ways -- invented counterexamples through unreachable callees, and a pointer dispatching where it never points -- and it was only visible once (2) stopped suppressing dispatch entirely. The definition now adopts the prototype's variable.

**Validation.** Reduced from the benchmark task to a 15-line repro before fixing anything. All three fixes have regression tests (`FunctionPointerReturnTypeTest`, 5 cases) verified to **fail on the old code and pass on the new**. No-overflow sample: **19 → 20 CORRECT, 11 → 8 ERROR (all 3 `ClassCastException`s gone), 0 WRONG**. Canaries 142/143 (the outlier being the known-slow `mod3.c.v+sep-reducer.c`). Module suites and `spotlessCheck` green.

Commits: `write an inlined call's result at the caller's type`, `a function's address needs a variable wide enough to hold it`, `initialise the address of a function declared before it is defined`.

⚠️ **Known limit, deliberately left**: dispatch still picks candidates by **arity alone**, so a pointer may still reach any same-arity address-taken function. That is an over-approximation (it can only *invent* errors, not miss them), but it is why the two `_44`/`_65` `_good` tasks now time out rather than verify -- the callees are genuinely explored for the first time. Narrowing the candidate set by parameter types is the obvious next step for that family.

## IMPLEMENTATION STATUS — batch 17 (the safety net came off, and what it was hiding)

The full run at `df43da466` (batches 1–9) landed: **correct 5,917 → 7,959**, **error 30,574 → 28,280**, but **wrong 13 → 78**. Of the 73 newly-wrong, **71 had previously been crashes** — and the split (45 false alarms, 12 missed bugs) is exactly the signature of the two function-pointer soundness bugs. Re-running all 73 against HEAD: **48 correct, 21 wrong, 4 error** — batch 16 clears the function-pointer wrongs; what remains is a memsafety/valid-free cluster.

Categorising the 11,589 error-status logs by first error showed ~7,000 already fixed post-run (`ParseCancellationException` 4,108; "Only structs expected here" 1,412; division overflow 1,075; pointer arithmetic 364; `ClassCastException` ~184). The largest **open** class was **"No such variable or macro" (1,375)**.

### The fallback is gone
`parseTypeAware` used to re-parse permissively when the strict parse failed, so that no file which parsed before could start failing. It also **hid every bug in the pass it was covering for** — it had already masked a collector bug that sent 19% of files down the old, wrong path with nothing said. Removed. If the strict parse cannot read a file, that is the answer.

Taking it off immediately surfaced two things it had been carrying:
- **Header typedefs were invisible to the parser.** `#include` is expanded at *visitor* time, long after parsing, so `pthread_mutex_t mutex;` could not be told from a multiplication and the file did not parse. The collector now follows an `#include` into the bundled header and harvests its typedefs — which is what a compiler's symbol table does anyway.
- **`XcfaToC` emitted `longlong`**, which is not C. `typeName` is the type's *internal* canonical name (the key the width table uses); printing it verbatim produced a file that does not parse. The permissive fallback had been taking `longlong` for a typedef'd type name.

### `T *p;` inside a block was a multiplication  (the 1,375)
957 of the 1,375 were typedef'd *type* names (`twoIntsStruct` 265, `example_user_t` 150, `u8` 74, `node_t`, `int64_t`, `FILE`, …), and they reduce to three lines:

```c
typedef int S;
int main(void){ S *p; p = 0; return 0; }   // "No such variable or macro: S"
```

`blockItem` listed `statement` before `declaration`, and ANTLR settles an ambiguity **by alternative order** — so `S * p;` became a multiplication whose result is discarded, `p` was never declared, and `S` reached the expression visitor as a *value*. C says the opposite: a block item that can be read as a declaration **is** one. Only *typedef* names were affected (`int *p;` and `struct T *p;` are safe — a keyword cannot begin an expression; and at file scope there is no statement to compete with), which is why the typedef work had not caught it.

The predicate is gated on knowing the type names — under the permissive collect pass every identifier is a "type name", where `f(x);` would answer yes and become "declare `x` of type `f`". Five new ambiguity tests pin the tree *shape*, and fail on the old grammar.

### The builtins (418 of the 1,375 were compiler builtins)
- **`__builtin_unreachable`** → `abort`: the path ends, which is the compiler's contract, and invents no error.
- **`__atomic_load_n` / `__atomic_store_n`** → the load and the store. The memory order constrains only reordering, and the analysis is sequentially consistent.
- **`__builtin_bswap16/32/64`** → the bytes, taken apart and concatenated back the other way. `BitwiseChecker` now marks a caller as needing bitvectors — reversing bytes means nothing to a mathematical integer.
- **`memcpy` / `memmove` / `memset`** (`MemoryFunctionsPass`) → the copy, spelled out. Nothing modelled them before: the havoc pass will not take a call with pointer arguments, so `memcpy` reached the analysis as a call to a function that does not exist and **brought it down**. The count is in *bytes* but memory is `arrays[base][index]` over *typed* elements, so it copies `n / sizeof(element)` elements. A symbolic count or a struct pointee is **not attempted** — it is left to fail loudly rather than move the wrong number of bytes.

Every model is pinned by a test that asserts its *semantics* and a **negative control** asserting the wrong value, which must come back Unsafe — "it parsed" proves nothing.

**Validation.** Canary parse sweep **143/143** with the fallback gone; canary verdicts **142/143** (the outlier is the known-slow `mod3.c.v+sep-reducer.c`); module suites and `spotlessCheck` green.

⚠️ **Still open**: `memcpy` with a *symbolic* count needs a real loop in the pass (new locations), and a struct pointee needs the flat object layout (AD7).

## IMPLEMENTATION STATUS — batch 18 (the wrong results: memsafety)

Going after the 21 wrong answers that survived batch 16. They split into **8 missed bugs** (we said Safe; there is a violation) and **13 false alarms** (we said Unsafe; there is none). Missed bugs first — they are the ones that cost.

### `free()` of non-heap memory was never detected  (5 missed bugs)
The check refused a null/negative pointer and one whose recorded size is 0. But `AllocaFunctionPass` *deliberately records a real size* -- it has to, or reads through an alloca'd block would look out of bounds -- so **`free(alloca(n))` sailed through as a perfectly good free**. The pointer model already partitions bases by residue mod 3 (`3k+0` malloc, `3k+1` alloca, `3k+2` an address-taken local), so `free` now also demands a heap base. `CWE401_Invalid_Free` ×4 and `memsafety-ext3/freeAlloca` all report Unsafe; so does `free(&local)`.

### `free(NULL)` was reported as an invalid free  (3 false alarms)
"If ptr is a null pointer, no action occurs" (C17 7.22.3.3) -- it is the idiom every cleanup path is written around. A null pointer has no recorded size, so the size bound took it for one that was never allocated. **Pre-existing** (confirmed by rebuilding without the change). Fixing it turned three `ldv-memsafety/memleaks_*` tasks Safe.

### `sizeof(struct)` returned 4, whatever the struct held
A struct's `width()` is pointer-wide -- it is the *handle* a struct is passed by, not its size. Allocation sizes come from `malloc(sizeof(struct node))`, and struct members are addressed by their **index**, so the fifth member of a five-member struct sat at offset 4 and the bound check read `4 < 4` and called a perfectly good access an invalid dereference. **A struct of four members or fewer never tripped it**, which is why it survived. `sizeof` now sums the members (a union takes its largest).

Commits: `only the heap may be freed, and freeing nothing is fine`, `a struct is as big as what is in it`.
**Validation**: canaries **142/143** (the known-slow `mod3.c.v+sep-reducer.c`), a **70-task sample of previously-correct valid-memsafety tasks 70/70**, module suites and `spotlessCheck` green. Both directions pinned: `free(malloc)`/`free(NULL)`/`free(realloc)` stay Safe; `free(alloca)`/`free(&local)`/double-free are Unsafe.

### The `weaver` data races — FIXED (3 false alarms), but they now time out
Commit: `an access to atomic memory is not a race`.

An access to an `_Atomic` object is not a data race with anything. The race is **not** found by `DataRaceToReachabilityPass` at all -- it is found by an *analysis-level* state predicate, `XcfaDataRaceCheck.getDataRaceDetector`, which inspects concurrent edges directly. That is why filtering dereferences in the pass changed nothing even with the filter demonstrably firing: it was filtering something the verdict never depended on. The detector has two branches, and only one of them looked:

```kotlin
// two global VARIABLES -- checks atomicity:
v1.globalVar == v2.globalVar && !v1.globalVar.atomic && ...
// two MEMORY LOCATIONS -- checked nothing:
(m1.access.isWritten || m2.access.isWritten) && canExecuteConcurrently(..) && mayBeSameMemoryLocation(..)
```

So a global `_Atomic int` was excluded, while `A[i]` through an `_Atomic int *A` was reported as **racing with itself**. The memory branch now reads the same flag the variable branch already did -- four lines, no new plumbing.

⚠️ **Two traps on the way, both worth remembering.**
- I first tried to read the atomicity off the *dereference's* recorded type. It is not dependable: `FrontendXcfaBuilder` types the deref on the **left** of an assignment as a *pointer to* the element while the one on the right is typed as the element, and types being keyed by the expression, **the two collide in the metadata**. The pointer's own declaration states it once, unambiguously.
- That insight also retired an earlier attempt (threading `ParseContext` through ~15 call sites, plus marking the pointee atomic in `NamedType`): the flag was already in the XCFA, sitting unused in the branch directly below the one that reads it.

**The honest result**: the three tasks go from **wrong (Unsafe, −16 each)** to **unknown (0)** -- they no longer invent a race, but they now *time out* rather than prove safety, even at the full 900 s budget. Removing a false alarm is not automatically a correct answer.

**Validation.** The dangerous direction here is a *missed* race, so the sample was chosen for it: **all 73** previously-correct `no-data-race` tasks that *expect* a race, plus 30 that expect none -- **103/103 correct**, no race missed. Canaries 142/143, module suites (including the data-race tests) and `spotlessCheck` green.

⚠️ Theta has one atomic flag per declaration, so `_Atomic int *p` (atomic pointee) and `int *_Atomic p` (atomic pointer) cannot be told apart. The former is what programs write, and that is how it is read.

### (superseded) the earlier diagnosis
An access to an `_Atomic` object cannot be a data race. A **global** `_Atomic int` is already excluded (`getPotentialRacingVars` filters on the *declaration's* flag), but `_Atomic int *A; A[i]` is reported as racing with itself. Root cause: **`CComplexType.setAtomic()` is never called anywhere** -- atomicity lives only on `CSimpleType`, so a dereferenced element has no atomic flag to read. Marking the *pointee* atomic in `NamedType.getActualType` (before the pointers are wrapped) does work -- verified `embedded=CSignedInt embAtomic=true` -- but filtering atomic dereferences in `DataRaceToReachabilityPass` **did not fix the task**, and instrumenting the pass showed why the fix is in the wrong place: in the concurrency portfolio the pass runs *post-hoc* through `optimizeFurther`, where `racingVars` is empty and **there are no `Dereference` exprs left at all**, yet a race is still reported. So the violation comes from somewhere else in that pipeline. Reverted rather than committed unproven; the diagnosis is the deliverable.

### Not attempted
`memsafety/cmp-freed-ptr` (1 missed bug) needs `malloc` to be *able* to return a previously freed address; Theta's allocator is a monotone counter that never reuses, so the double free is unreachable in the model. That is an allocator change with a wide blast radius, for one task.

`free(realloc(p, n))` **crashes** (`IllegalArgumentException`) -- pre-existing, `realloc` is not modelled at all.

## IMPLEMENTATION STATUS — batch 19 (`_Atomic` is a property of a *level* of a type)

Commit: `_Atomic attaches to a level of a type, not to a declaration`.

The weaver fix (batch 18) leaned on a quirk: `_Atomic int *A` happened to set the *variable's* atomic flag, and the memory check read that. It worked, but it could not tell the two apart —

```c
_Atomic int *p;   // p is an ordinary variable; p[i] is atomic and cannot be raced on
int * _Atomic p;  // p itself is atomic; p[i] is not, and can be
```

— and getting that backwards either invents a race or hides one. `_Atomic` is not one flag on a declaration; it attaches to a **level** of a type, and C gives four ways to say where. Theta could represent none of them: `CSimpleType` had a single `atomic` boolean, `CComplexType.setAtomic` was **never called anywhere**, `visitTypeSpecifierAtomic` **threw "Not yet implemented"** (so `_Atomic(T)` did not work at all), and any qualifier after a `*` threw *"pointers should not have type qualifiers!"*.

### What the model now says
`CSimpleType` records atomicity **per pointer level** plus the base, and distinguishes pointers written as `*` in *this* declaration from pointers inherited with the type (a typedef of a pointer). That distinction is what makes `_Atomic int *p` (the `*` is this declaration's, so the qualifier reached only the `int`) different from `int_ptr _Atomic p` (the pointer came with the typedef, so the qualifier applies to *it*). `NamedType`/`Struct` then set `CComplexType.setAtomic` on the level it was written at.

- `_Atomic int x` / `int _Atomic x` / `_Atomic(int) x` — an atomic int
- `_Atomic int *p` / `_Atomic(int) *p` — a plain pointer to an atomic int
- `int * _Atomic p` / `_Atomic(int *) p` — an **atomic pointer** to a plain int
- `_Atomic int * _Atomic p` — both; `int * _Atomic * p` — only the inner one
- `typedef _Atomic int atomic_int;` and `int_ptr _Atomic p` — through typedefs
- mixed with `const`/`volatile`, in any order

### What reads it
Two *different* questions, and they now get different answers:
- a race between two **variables** is excluded when the *variable's own* type is atomic — so `XcfaGlobalVar.atomic` is now `actualType.isAtomic` (the outermost level), not the declaration's base flag;
- a race between two **memory locations** is excluded when the **pointee** is — read off the pointer's type, which needed `ParseContext` threading into `getXcfaErrorDetector`. A caller without one only makes the check *more* conservative (report the race), never less: nothing recorded means nothing skipped.

### Validation
Test-driven: `CAtomicTypeTest` (25 placements, asserting the type with an `_` on every atomic level) went **3/25 → 25/25**; `AtomicRaceTest` pins the same six at the XCFA, where the checks actually read them. End to end, all six race programs answer correctly — including the discriminating pair, where `_Atomic int *A` makes `A[0]` race-free while `int * _Atomic A` still reports the race on it.

Regression: canaries **142/143**, the data-race sample **103/103** (all **73** tasks that *expect* a race still catch it — a missed race is the dangerous direction here), memsafety **70/70**, all module suites and `spotlessCheck` green.

### C11 `<stdatomic.h>` — also done
Commit: `model C11 stdatomic, and keep an address-taken atomic atomic`.

The header is bundled (`atomic_int` &c. are ordinary `_Atomic` typedefs, `memory_order` an int whose constants come from `MacroExprs`). The *operations* are type-generic, which C expresses with macros and this grammar cannot express at all, so they are recognised by name and built directly: `atomic_load`/`store`/`init`, `atomic_fetch_add`/`sub`, `atomic_exchange`, and the `_explicit` variants -- alongside the `__atomic_*` builtins they compile down to. A read-modify-write yields the value that was there **before**, which every test pins with a *negative control* asserting the new one (it must come back Unsafe).

### ⚠️ The reason this fought back: C types are keyed by object *identity*
`FrontendMetadata` keys them with `System.identityHashCode`. **Any pass that rebuilds an expression loses its C type**, and `CComplexType.getType` then quietly falls back to inferring one from the SMT sort -- where an `_Atomic int` is indistinguishable from an `int`. That one fact explains three dead ends at once:
- reading atomicity off a **dereference** cannot work (passes rebuild them);
- reading it off a **`RefExpr`** can (a `VarDecl`'s `ref` is a cached instance);
- and `atomic_int x` touched through `&x` failed *both* ways, because `ReferenceElimination` folds `&x` to a bare **literal** -- the object's id -- which carries nothing at all.

So the fact is now *recorded where it is known* rather than recovered later: `XcfaGlobalVar` gained **`pointsToAtomic`**, set by `ReferenceElimination` on the pointer it invents for an address-taken variable, and the race check resolves a pointer either as a variable or as that folded id. (This identity-keying is worth remembering -- it is a trap for anything else that tries to read a C type after the passes have run.)

**The matrix, all 8 correct** -- and the last three are the ones that prove the filter is not simply skipping everything:

| program | verdict |
|---|---|
| `atomic_int x` + `atomic_fetch_add(&x,1)` | no race ✓ |
| `atomic_int x`, plain `x = x+1` | no race ✓ |
| `_Atomic int *A`, `A[0]` | no race ✓ |
| plain `int x` via `&x` | **races** ✓ |
| `int * _Atomic A`, `A[0]` | **races** ✓ |
| plain `int *A`, `A[0]` | **races** ✓ |

Regression: canaries **142/143**, data-race sample **103/103** (all **73** race-expecting tasks still caught), memsafety **70/70**, all module suites and `spotlessCheck` green.

## IMPLEMENTATION STATUS — batch 20 (the sweep was measuring the wrong backend)

Nothing here is a code change. It is the third fake result this harness has produced, and the worst,
because it was the *green* numbers that were fake.

**The real SV-COMP invocation** — read it off the `options=` attribute of any BenchExec result XML in
this directory:

```
options="--svcomp --portfolio STABLE --loglevel RESULT"
```

**Every verdict script written before today passed neither flag.** The CLI's default backend is plain
`CEGAR` (`XcfaConfig.kt`, `var backend: Backend = Backend.CEGAR`), *not* the portfolio — so the canary,
memsafety and data-race sweeps have all been scoring a configuration the competition never runs.

This does not merely lose coverage; it **invents failures**. The smallest struct program in C —

```c
struct S { int a; int b; };  s.a = 5;  if (s.a != 5) reach_error();
```

— cannot be verified under the default backend: the EXPL domain cannot track the memory arrays, the
same counterexample recurs, and `CexMonitor` throws `NotSolvableException`. Under `--portfolio STABLE`
it is **Safe in seconds**, because the portfolio falls through EXPL to PRED_CART. Master does exactly
the same, so it is not a regression — it is the harness lying. (This is also what the "known-slow"
`mod3.c.v+sep-reducer.c` canary was: not slow, just given the wrong backend.)

A second, smaller harness bug fell out of the same re-run: the memsafety sweep compared Theta's
`Safe`/`Unsafe` against an expectation of `false(valid-free)`, i.e. it never checked the **subproperty**
— and SV-COMP scores `false(valid-deref)` where `false(valid-free)` was expected as a *wrong* answer.
Theta does print it (`(Property valid-free)`); the script now reads it (`verdict_pf_ms.sh`).

**Re-validated under `--svcomp --portfolio STABLE`** (scripts: `verdict_pf.sh`, `verdict_pf_yml.sh`,
`verdict_pf_ms.sh`):

| suite | result | note |
|---|---|---|
| canaries | **143/143** | up from the 142/143 the wrong backend reported |
| memsafety | **70/70** | now subproperty-aware — a *stricter* check than before |
| data-race sample | **103/103** | all **73** race-expecting tasks still caught |

So the branch is green on the configuration that actually gets scored, and the earlier green numbers,
though measured wrongly, were not hiding a regression.

**The rule going forward:** before believing any local verdict number, diff the harness against the
real `options=` string. A green sweep from the wrong configuration is worse than no sweep, because it
gets trusted.

### The two "over-approximations" the batch-19 note warned about — both were mis-flagged

Probed directly (`scratchpad/probe/`), and neither can produce a wrong answer:

| Probe | Expect | Got |
|---|---|---|
| two same-arity address-taken fns, `fp = f`, assert `f`'s effect | Safe | Safe ✓ |
| ditto, assert the call did *not* happen | Unsafe | Unsafe ✓ |
| fp reached through a struct member | Safe | Safe ✓ |
| `union {int a; int b;}`, `u.a=5`, assert `u.b==5` | Safe | Safe ✓ |
| ditto, assert `u.b!=5` (they *must* alias) | Unsafe | Unsafe ✓ |
| `union {int a; char c;}` — mixed representation | rejected | Frontend failed ✓ |

- **Function pointers are not over-approximated.** Every dispatch branch carries
  `assume(fp == id(f))` — an *exact* equality on the pointer value — so a candidate that is not the
  real target is an **infeasible branch, not a spurious behaviour**. The broad candidate set costs
  *state space* (each candidate inlines a full copy of the function at every indirect call site,
  which is what makes the Juliet `_44`/`_65` families time out), never soundness.
- **Unions are not over-approximated either.** Same-representation members genuinely alias — which is
  what C says — and mixed-representation members are *rejected loudly*, not answered. The 265 punning
  errors **are** that refusal.

**Consequence for the queue — item 3 was pointing the wrong way.** Narrowing the function-pointer
candidate set by parameter types is the *dangerous* change, not the safe one. Extra candidates are
free, because the guard refutes them; narrowing can only ever **remove the true target** (a program
casting through `void *`, or `int` vs `long`), and the no-match branch is
`assume(fp != every id); havoc ret` — so the call, *and all of its side effects*, silently vanishes.
That is a missed bug. It trades a timeout problem for a soundness problem, and must not be done blind.
If it is done at all, the no-match branch has to stop being a silent havoc first.

## BENCHMARK — the full re-test (2026-07-13_19:02, HEAD ≈ batch 19, portfolio STABLE)

Downloaded to `benchmark-results/results-2026-07-13_19-02/` (`runs_new.tsv`, `compare.py`). Same task
set as the batch-8 baseline (36,602 runs each), same `--svcomp --portfolio STABLE --loglevel RESULT`,
same 900 s / 8 GB — so the diff is code-only. **The portfolio config is unchanged since the baseline**
(no post-baseline commit touched `cli/portfolio/` or `cli/params/`), which matters for the regression
below.

| bucket | OLD (batch 8) | NEW (batch 19) | Δ |
|---|---|---|---|
| correct | 5,917 | **8,356** | **+2,439** |
| wrong | 13 | **28** | +15 |
| unknown | 27 | 358 | +331 |
| error: frontend, before parse | 14,539 | 7,649 | **−6,890** |
| error: frontend, after parse | 2,960 | 1,324 | −1,636 |
| error: solver | 31 | 45 | +14 |
| TIMEOUT | 10,607 | 16,827 | +6,220 |
| OUT OF MEMORY | 2,437 | 1,944 | −493 |

**The frontend win is real and large**: crashes nearly halved (17,499 → 8,973, −8,526). Biggest error
drops by family: Juliet −6,693, hardness −315, termination-memory-alloca −186, nla-digbench-scaling
−138 (→0), weaver −110, bitvector −52 (→0). Juliet alone accounts for **+3,362 correct**.

### The regression the headline hides: unreach-call correct −950

Per property, correct moved: no-overflow **+2,769**, valid-memsafety +563, valid-memcleanup +24
(new), termination +21, no-data-race +12, and **unreach-call −950** (3,113 → 2,163). That last is a
genuine loss, not displacement: **1,119 tasks went correct → TIMEOUT**, concentrated in the
boolean/input-heavy families — hardness (470) and eca-rers2012 (360). 165 of them solved in **under
90 s** in the baseline (one in 11 s) and now exhaust 900 s: a 10–60× analysis-time blow-up, not
near-limit noise. Reproduced locally (the 11 s task runs past 200 s on HEAD).

**Isolation so far:**
- *Not the parse.* 813/815 sampled regressors have the Portfolio column set — the frontend finished;
  they time out in the **analysis**.
- ~~*Not the short-circuit `&&`/`||` change.*~~ **This was wrong** (see batch 23): `git bisect` found
  `89020cef2` — the short-circuit commit — to be the *first bad commit*, for every profile. I had
  ruled it out from a hand-made example whose operands were unparenthesised, which is precisely the
  case that does not trigger it. **A negative result from a synthetic test is not evidence.**
- *Not profile selection.* 1,114/1,119 kept the same arithmetic profile (FLOAT 374, LIN_INT 290,
  NONLIN_INT 288, BITWISE 128, …). The portfolio routes them exactly as before.
- **Multi-cause, spanning every profile.** The prime suspect for the integer profiles is the
  **range-constraint on havoc** (`7201af3fa`, `TypeRange.kt`): it stamps a `[−2³¹, 2³¹]`-magnitude
  bound on every nondet input, which is exactly the large-constant material that makes interpolation
  wander — and the generated XCFA shows it emitted **twice** per nondet (a duplication bug worth
  fixing regardless). But it is documented as a no-op under bitvector arithmetic, so it **cannot**
  explain the 128 BITWISE regressors; those point at the other broad post-baseline change, the
  `Pos()`/`bvpos` wrapping of no-op bitvector casts (`de357dedb`). Confirming this needs a
  build-and-time experiment (neutralise `withinTypeRange`, and separately the `Pos` wrap, re-time the
  fast hardness/eca tasks) — **not yet done**.

### Wrong results: 13 → 28 (8 of the old 13 fixed, 5 persisted, 23 newly wrong)

Fixed by this branch: the two `signextension2` bitvector tasks (the U-suffix fix, now **correct**),
`memleaks_test3-1` (correct), `nondet_struct` (no longer wrong — now an error), and four of the W5
`valid-deref` cluster moved wrong → **timeout** (hostid, hyperkit_1Fixed, getNumbers1-2, Stockholm-2)
— unknown scores 0, wrong scores negative, so that is progress.

The 28 split **6 missed bugs / 22 false alarms**. Newly wrong by family: aws-c-common 9 (false
alarms; PLAN had catalogued 3 — the rest were crashing before), **termination-memory-alloca 5** (a
**new** false-`valid-deref`/`no-overflow` cluster from the alloca model: easySum-alloca, genady-alloca
×2 props, java_Nested-alloca, java_Sequence-alloca), memory-model 2SB/4SB (known missed bugs),
Juliet CWE121 `_66_good` ×2 (known), memsafety/lockfree-3.0 (known), and three genuinely new ones:
goblint 09-regions (missed race), termination-nla/dijkstra6-both-nt (missed overflow),
memsafety-cve/admeshFixed (false valid-deref). The two OC tasks (pthread/singleton, goblint
04-mutex) persist and are now **in scope** (OC PR merged 2026-07-16).

## IMPLEMENTATION STATUS — batch 22 (the unreach-call regression was a *doubled* range assume)

Commit: `stop annotating a nondet havoc's range twice`.

The −950 unreach-call regression (batch 21) isolated cleanly. Building HEAD with the range-constraint
toggled off (`withinTypeRange` → empty) in a worktree and re-timing the fast regressors under
`--portfolio STABLE` (scratchpad harness) showed:

| profile | task | HEAD | range **off** |
|---|---|---|---|
| NONLIN_INT | `mod3.c.v+sep-reducer` | timeout | **Safe 4 s** |
| NONLIN_INT | `hardness_codemodifications_normal_file-56` | timeout | **Safe 77 s** |
| FLOAT | `hardness_operatoramount_..._file-83` | timeout | timeout |
| BITWISE | `hardness_floats_no_floats_file-114` | timeout | timeout |

So the integer-arithmetic profiles (LIN_INT + NONLIN_INT ≈ **578** of the 1,119 regressors) were the
range constraint; FLOAT/BITWISE are a *separate*, still-open cause (the Pos/bvcast wrap partly
recovers one BITWISE task but not another — inconclusive, needs a git-bisect). **The FLOAT/BITWISE
regression is NOT fixed.**

**But the root cause was subtler than "the constraint is expensive": it was applied *twice*.**
`NondetFunctionPass` annotated each nondet havoc with `withinTypeRange`, and `HavocPromotionAndRange`,
which runs after it and bounds *every* havoc, annotated it again — two identical
`assume(±2^31 ≤ x ≤ ±2^31)` per nondet. A *single* copy is fine (`mod3` solves in 4 s with the range
still on, just once); the duplicate is what wrecked interpolation. The fix is one edit — drop the
redundant annotation from `NondetFunctionPass`, leave `HavocPromotionAndRange` as the sole, unconditional
emitter — so **no property gating, no soundness change**: the range is still there once, for every
property, exactly as intended.

*(A first attempt gated the constraint off for reachability entirely; it recovered `file-56` but broke
`mod3`, which needs the single copy. The de-dup is strictly better and was reverted to.)*

Validation: module suites (`PassTests`, `UnresolvedInvokeToHavocTest`, `NondetMemoryTest`) green;
the two NONLIN regressors recover to correct **Safe** (3 s, 81 s); **canary 143/143** under
`--svcomp --portfolio STABLE` (no verdict flips — expected, since the change only removes a redundant
identical assume).

## IMPLEMENTATION STATUS — batch 23 (the rest of the regression: a guard on operands that do nothing)

Commit: `only short-circuit an operand that does something`.

Batch 22 left FLOAT (~374) and BITWISE (~128) unexplained. **`git bisect` settled it** (harness:
`scratchpad/bisect_test.sh`, builds each candidate and times `file-83`/`file-114` under
`--portfolio STABLE`; log in `scratchpad/bisect.log`):

```
de357dedb  FLOAT=CAP    BITWISE=CAP
a1a25d0eb  FLOAT=CAP    BITWISE=CAP
5ec80d8d0  FLOAT=Safe/4s  BITWISE=Safe/8s   <- good
7201af3fa  FLOAT=CAP    BITWISE=CAP
8ef2e2975  FLOAT=CAP    BITWISE=CAP
89020cef2  FLOAT=CAP    BITWISE=CAP        <- first bad
```

**`89020cef2` "evaluate the operands of && and || under their short-circuit" is the first bad commit**,
for *both* profiles. (I had "ruled it out" in batch 21 from a synthetic test that was too simple —
a reminder that a negative result from a hand-made example is not evidence.)

### The bug

`guardShortCircuited` took *"did `preStatements` grow?"* as its signal for "this operand has side
effects, so it must go behind the short-circuit". But a statement lands in `preStatements` for
reasons that have nothing to do with side effects: **`visitPrimaryExpressionBraceExpression` lifts one
for every parenthesised sub-expression.** So `(a >= 1) && (a <= 2)` — pure — got a guard, and the
guard is a *branch*: the XCFA went from one straight-line edge to a two-armed split **whose arms were
identical**. `(a && b) || (c && d)` is exactly how SV-COMP writes `assume_abort_if_not`, and file-83
has four of them: 2⁴ paths, 11 s → timeout.

Confirmed minimally: `a >= -100 && a <= -1` does **not** grow the model; `(a >= -100) && (a <= -1)`
does (2 nodes/1 edge → 3/3).

### The fix

Guard an operand only when its lifted statements *do* something — a call, an assignment — which is
what the commit's own doc says it is for ("calls do"). A bare expression is only there because it was
parenthesised, and running it either way is unobservable. The predicate must look in each statement's
`getPreStatements()`/`getPostStatements()` slots too: **that is where a parenthesised call keeps its
call**, and a first version that missed them silently un-guarded `(a != 0) && (bump())` — reintroducing
the very wrong result `89020cef2` had fixed. The negative control caught it.

### Result — every regressor recovers, and beats the baseline

| profile | task | baseline | HEAD (broken) | fixed |
|---|---|---|---|---|
| FLOAT | `..._operatoramount_..._file-83` | 11 s | timeout | **6 s** |
| FLOAT | `..._operatoramount_..._file-42` | 14 s | timeout | **5 s** |
| BITWISE | `..._floats_no_floats_file-114` | 30 s | timeout | **8 s** |
| BITWISE | `..._floats_no_floats_file-68` | 36 s | timeout | **16 s** |
| NONLIN_INT | `..._codemodifications_..._file-56` | 21 s | timeout | **7 s** |
| NONLIN_INT | `mod3.c.v+sep-reducer` | 13 s | timeout | **3 s** |

All **Safe** (correct). So the short-circuit bug was the dominant cause across *every* profile — the
batch-22 range de-dup is still right and still needed (it is what took `file-56` from timeout to 81 s
on its own), but this is what takes them all below the baseline. **The −950 unreach-call regression
should be gone, and then some.**

Validation: new **`ShortCircuitTest`** pins both directions — a parenthesised *comparison* must add no
branch, a parenthesised *call* must still be guarded — and **fails on the unfixed code** (verified by
reverting). Canary **143/143**; `theta-c-frontend`, `theta-c2xcfa`, `theta-xcfa` suites and
`spotlessApply` green.

## IMPLEMENTATION STATUS — batch 24 (`for (*p = 0; ...)` was parsed as a declaration)

Commit: `a for-init that assigns through a pointer declares nothing`. **GRAMMAR CHANGE — handled per
the protocol below.**

The five `termination-memory-alloca` false-`valid-deref` results (batch 21) were never about alloca.
Reduced to a minimal program, then found by instrumenting `SimplifyExprsPass` to print its constant
valuation — which showed **two** variables named `i`:

```
localVars      = [..., main::i, ..., main::for0::i, ...]
constValuation = ... main::i=5, main::for0::i=0, ...
```

`main::i` is the real pointer (correctly 5). `main::for0::i` is a *second*, for-scoped `i` — value
**0**. So `for (*p = 0; ...)` was being parsed as an **implicit-int declaration** `int *p = 0;`,
declaring a fresh NULL pointer that shadows the real one for the whole loop. Every `*p` in the body
then dereferenced base 0 (the unallocated class) and the deref check fired: **a safe program reported
Unsafe.**

### The bug

```
typeSpecifierPointer :  typeSpecifier? pointer ;    // the type specifier is OPTIONAL
forInit              :  forDeclaration | expression? ;   // declaration tried FIRST
```

The optionality is needed — it is what lets the `*` in `unsigned *p` follow a specifier that is
already there — but it also makes a **bare `*` a declaration specifier all on its own**. Nothing in C
begins a declaration with `*`; `for (*p = 0; ...)` begins an expression with one. `blockItem` was
given a `startsDeclaration()` guard in batch 17, which is exactly why the same assignment *as a plain
statement* always worked; `forInit` never got one. Hence the oddly specific trigger: a loop **and** a
write to the pointee **through the for-init**.

### The fix

A `startsForDeclaration()` predicate on the `forDeclaration` alternative: a leading `*`/`^` is never a
declaration; otherwise defer to `isTypeStart`. `for (int i = 0; …)`, `for (int *p = q; …)`,
`for (myptr p = q; …)` (typedef), `for (i = 0; …)` and `for (;;)` all keep their old parse.

### Validation (grammar HANDLE WITH CARE protocol)

- **One construct, one commit.** ✓
- **Parse-tree shape, not "it parsed":** 3 new cases in `CTypeNameAmbiguityTest` assert whether a
  `ForDeclarationContext` is present — **23/23** (was 20).
- **Byte-identical XCFA for programs not exercising the construct:** built a jar with and without the
  grammar change and diffed `xcfa.json` over all 143 canaries (`scratchpad/xcfa_equiv.sh`):
  **103 IDENTICAL, 0 newly-broken, 0 unexpected diffs.** (4 first showed as "newly builds"; re-run
  serially they are IDENTICAL too — parallel-load flakiness, *again*.)
- Canary verdicts **143/143**; `theta-c-frontend`, `theta-c2xcfa`, `theta-xcfa`, `spotlessApply` green.

### Result on the five wrong results

| task | property | was | now |
|---|---|---|---|
| `genady-alloca` | no-overflow | **wrong** | **Safe ✓ correct** |
| `easySum-alloca` | valid-memsafety | **wrong** | timeout |
| `genady-alloca` | valid-memsafety | **wrong** | timeout |
| `java_Nested-alloca` | valid-memsafety | **wrong** | timeout |
| `java_Sequence-alloca` | valid-memsafety | **wrong** | timeout |

All five false alarms are gone; one is now correct. The four timeouts are at a 200 s local cap, not
SV-COMP's 900 s — they may well solve there, but **I have not shown that**, so they are recorded as
timeouts. Wrong scores negative and a timeout scores zero, so this is a strict improvement either way.

**Newly exposed (not a regression, previously masked by the false alarm):** the same loop written with
an *address-taken local* rather than `alloca` (`int s; int *p = &s; for (*p = 0; ...)`) now reaches
the analysis and fails there with `IllegalStateException: Incomplete dereferences (missing
uniquenessIdx)`. An error, not a wrong answer — but it is the next thing in this area.

## Run 2026-07-20_22-41-batch51 (sosy, 5750G, batches 47–51) — the initializer fix confirmed, **and a 6-task soundness regression in multi-dim VLAs**

First run to measure batches 47–51 at scale (pointer-to-array, aggregate array elements, multi-dim
arrays, sub-word union overlay, the brace-initializer fix). Compared against
`results-2026-07-20_15-44-batch46`:

**Correct 10,277 → 10,308 (+31). Error 25,929 → 25,891 (−38). Unknown 368 → 369. Wrong 28 → 34 (+6).**

Two of the three checks pass, and the third fails in the way that matters most.

**(a) The batch-51 fix is confirmed.** Total frontend-failed **6,661 → 6,544 (−117)**, and the three
directories the batch-46 regression hit moved exactly as predicted: `ldv-memsafety-bitfields`
**5 → 0**, `ldv-linux-3.4-simple` 586 → 565, `ldv-challenges` 198 → 197.

**(b) Correct recovered and beat the pre-regression baseline** — 10,308 against batch 43's 10,288.
Transition directions confirm this is real rather than luck: deterministic frontend moves are
**+30 error→correct against −3 the other way**, while timeout/OOM flips are symmetric noise
(27 in, 23 out).

**(c) The wrong-set is NOT clean: 6 newly wrong, 0 fixed.** `test-bitfields-1-1` is still correct,
so batches 45–46 hold, but every new wrong is an array task:

| task | was | now | expected |
|---|---|---|---|
| `array-patterns/array13_pattern` | frontend failed | **false(unreach-call)** | true |
| `array-patterns/array15_pattern` | frontend failed | **false(unreach-call)** | true |
| `array-patterns/array27_pattern` | frontend failed | **false(unreach-call)** | true |
| `array-patterns/array28_pattern` | frontend failed | **false(unreach-call)** | true |
| `array-patterns/array30_pattern` | frontend failed | **false(unreach-call)** | true |
| `array-multidimensional/init-non-constant-2-n-u` | frontend failed | **false(unreach-call)** | true |

All six are **multi-dimensional VLAs** — `int array[ARR_SIZE][ARR_SIZE]`, `unsigned A[m][n]` — and
all six are `error → wrong`, one-directional, so this is deterministic, not noise.

**Root cause (batch 49, mine).** The flat model lowers `a[i][j]` to `arrays[a][i*rowLen + j]`, and
`rowOf` needs `rowLen` as a compile-time constant. For a VLA there is none, so `constantArrayLength`
returns null, `rowOf` returns null, and the code **falls through to the old row-object model**:
`arrays[arrays[a][i]][j]`. Those row bases are never allocated — `allocateArrayElements` only covers
`CStruct` elements with a constant count — so they are unconstrained and the solver may make `a[0]`
and `a[1]` the same base. Two rows alias, the summation loop reads back the wrong values, and the
assertion is spuriously violated. This is the *same* class of bug batch 48 fixed for arrays of
structs ("bases left unconstrained, so the solver could conflate two elements"); the VLA path slips
past it because `rowOf` bails out before reaching the flat model at all.

Before batches 47–49 these tasks died in the frontend, so the unsoundness existed but was masked.
Unlocking them exposed it — the frontend work did not create the hole, it removed the lid.

**Score impact is negative overall despite +31 correct.** A false alarm scores −16 in SV-COMP, so
six of them is −96, against roughly +40 for the correct gains. **This branch should not ship in
this state.**

**Fix, in order of preference:**
1. **Use the symbolic dimension** — `i*ARR_SIZE + j` is a perfectly good expression; nothing
   requires `rowLen` to be a literal. Keeps the tasks unlocked *and* sound. Caveat to handle: C
   fixes a VLA's size at declaration, so a later reassignment of `ARR_SIZE` must not retroactively
   change the layout — capture the dimension into a temporary at declaration.
2. **Failing that, reject** a non-constant multi-dim row length outright. That returns these tasks
   to ERROR (score 0) instead of a wrong answer (−16) — the same "fail loudly rather than answer
   wrongly" call as batch 45's initializer guard, which the batch-46 run vindicated.

Also worth noting: **3 `ldv-linux-3.4-simple` tasks regressed correct → `frontend failed, before
parsing finished`** (two `dib3000mc`, one `max8649`). Small and deterministic, so real, but
unrelated to the array issue and not yet diagnosed.

## Run 2026-07-20_15-44-batch46 (sosy, 5750G, batches 45–46) — bitfield packing confirmed, **and a 36-task regression found**

Full 36,602-run integer run on the batch-46 archive (bitfield storage units + slicing, union
overlay). Compared against `results-2026-07-19_22-01-batch43`:

**Correct 10,288 → 10,277 (−11). Wrong 29 → 28 (−1). Error 25,916 → 25,929 (+13). Unknown 369 → 368.**

**The wrong-set check passes cleanly: 0 newly wrong, 1 fixed** — and the one fixed is exactly
`ldv-memsafety-bitfields/test-bitfields-1-1` (valid-memsafety), the false alarm the whole
storage-unit + slicing design was built to kill. The core struct-model rewrite introduced **zero**
new wrong answers, which was the risk that mattered most. Soundness held.

But the correct count went *down*, and that is not noise. Decomposing the 108 category transitions:

| transition | count | nature |
|---|---|---|
| correct → error (timeout/OOM) | 32 | resource boundary |
| error → correct (timeout/OOM) | 45 | resource boundary |
| **correct → ERROR (frontend failed)** | **25** | **deterministic regression** |
| frontend-failed → correct | **0** | — |
| wrong → correct | 1 | `test-bitfields-1-1` ✓ |
| unknown ↔ other | 4 | mixed |

Resource flips are symmetric noise and actually net **+13 in batch-46's favour**. The real signal is
one-directional: **36 tasks newly frontend-fail, 0 newly recover** (total frontend-failed 6,625 →
**6,661**). Root cause is a **single** guard, identical across all 36 logs:

```
UnsupportedFrontendElementException: Brace initializer for a struct with packed bitfields
is not supported: <name>   (FrontendXcfaBuilder.kt:672, thrown from initializeGlobalVariable:615)
```

Distribution: **30 `ldv-linux-3.4-simple`** (CIL-generated drivers, struct-heavy), **5
`ldv-memsafety-bitfields`** (`test-bitfields-3-1`, `-3-2`, `-3.1-1` across termination +
valid-memsafety), **1 `ldv-challenges`**.

This is self-inflicted and was a deliberate batch-45 choice: once bitfields pack, a brace
initializer's elements no longer map one-to-one onto storage cells (member index ≠ unit index), so
rather than silently mis-initialize I threw. Failing loudly was the right call over answering
wrongly — the zero-new-wrongs result above is partly *because* of it — but it traded 36 previously
correct//progressing tasks for errors, so it must not stand as the end state.

**Fix (next):** splice each initializer element into its unit's cell via `BitfieldSlice.write`
at its slot's bit offset, accumulating per unit — the same read-modify-write machinery already used
for the bitfield *assignment* path in `CAssignment`. Then the guard can go. Requires the usual
gate: both encodings, 255 canaries, 14 fixtures, module tests.

**Net honest read:** batches 45–46 delivered the wrong-result fix they promised with no soundness
cost, but are **net −11 correct** until the initializer regression is repaired. Not shippable as-is.

## Run 2026-07-19_22-01-batch43 (sosy, 5750G, batches 38–44) — the batch-42–44 confirmation

Full 36,602-run integer run on the batch-43 archive (= all of batches 38–44; the tool dir is
named Theta-svcomp-43 but predates the switch fix's commit by minutes — it contains 38–44's
frontend work). Compared against the 2026-07-19_15-36 run (batches 38–41):

**Correct 10,118 → 10,288 (+170). Wrong 29 → 29. Error 26,090 → 25,916 (−174).**

The wrong set is **identical** — 0 fixed, 0 new. This is the clean signature of batches 42–44:
they are parse/frontend unlocks (arithmetic-cast fix, union punning, `__builtin_object_size`,
switch-width, initializers), which turn ERRORs into results without touching verdict logic, so
+170 error→correct and **zero** effect on wrongs. Confirms no regressions from any of the six
commits since 15-36, and that the batch-42–44 care (soundness checks, canary fixtures) held.

**Implication for the bitfield decision:** the 29 wrongs are unchanged and still include the
test-bitfields memsafety false alarms — the parse/frontend batches cannot move them. The only
remaining lever on the wrong count is the deferred bitfield storage-unit + slicing work (which
also unlocks the 865+84 TDX `memberOffset` cluster). That decision now has its confirming data.

## Batch-44 parse re-measure — accurate current cluster ranking + strategic state

Clean sweep of all 3,173 former parse-death inputs on the batch-44 jar: **988 PARSE-OK** (777 @
b39 → 888 @ b41 → 988 @ b44), **2,132 FRONTEND**, 51 parse-timeout, **2 parse-error** (the K&R
pair). The OOM cluster is gone (Struct.getActualType memoization). Frontend-crash ranking:

| runs | signature | nature |
|---|---|---|
| 865 | `memberOffset` (union punning) | **deferred bitfield**: TDX `union { u16 raw; struct {bits} }` — a narrow raw overlapping a bitfield-struct member the model stores as a pointer-wide base id. Needs storage-unit + slicing (batch 43-design). Also fixes the test-bitfields **wrongs**. |
| 734 | `ReferenceElimination.*` | **architectural (AD2)**: bare use of a split address-taken variable in pointer arithmetic. |
| 472 | `visitPostfixExpressionBrackets` | 441 = **neural-networks** `float (*A)[4]` pointer-to-array 2-D indexing ("Non-array expression used as array": the frontend flattens pointer-to-array to a plain pointer, losing the inner dimension). Low verdict-ROI — these nets time out even when parsed. |
| 127 | `visitPrimaryExpressionId` | undeclared library functions (malloc/memcpy in stripped goblint-coreutils). Low ROI (huge files, other barriers), return-type-guess risk. |
| 84 | `visitPostfixExpressionPtrMemberAccess` | same TDX bitfield family. |
| 42 | `CComplexType.getType` | small, mixed. |
| 30 | `visitPrimaryExpressionBuiltinVaArg` | va_arg on a local. |
| 26 | `FunctionVisitor.visitBodyDeclaration` | struct fed an `UnsupportedInitializer` (nested-init). |

**Strategic read:** the easy, high-verdict-ROI frontend/parse wins are exhausted (b38–44 took
parse deaths 4,108 → 2 and cleared union punning, cast, switch, initializers, builtins). What
remains is (a) the **deferred bitfield storage-unit + slicing** — the *only* remaining lever on
actual WRONGS (test-bitfields) and simultaneously the largest cluster (865 + 84 TDX), but a
high-blast-radius core-model change; (b) **AD2 split-variable arithmetic** (734, architectural);
(c) **neural-networks pointer-to-array** (441, low-ROI timeouts); or (d) small mixed clusters.
No further low-risk high-ROI single fix is visible. The next big step is a deliberate
investment decision: greenlight the bitfield work (with its regression risk, mitigated by the
scoping in batch 43-design + the fixtures/guard-set net) vs consolidate. Batch-43's benchmark
(in flight) will confirm the b42–44 wrong-count before that call.

## Run 2026-07-19_21-29-bw (sosy, 5750G, batch-42, forced `--arithmetic bitvector`)

Full 36,602-run bitvector run, to compare against the integer/`efficient` verification run
2026-07-19_15-36 (batch-38..41). Builds differ by batch-42 (a bitvector-only cast fix) — the
frontend parse fixes in 42–44 don't touch the already-parsing tasks these findings concern, so
the encoding comparison is valid for them.

**Totals: 8,650 correct / 37 wrong / 27,340 error / 575 unknown** vs int's 10,118 / 29 / 26,090
/ 365. Bitvector is more precise but much slower: the dominant shift is **1,984 correct→error**
(timeouts — bit-blasting is expensive) against **681 error→correct** (precision wins). Net it
loses ~1,470 correct.

### bw-vs-int verdict disagreements (the encoding-correctness audit — NOT yet fixed)

Wrongs are the concern. **29 tasks are wrong under bitvector but not under integer**
(encoding-induced), and **21 are wrong under integer but not bitvector** (encoding fixes):

- **no-overflow is bitvector's weak spot: 18 encoding-induced wrongs.** 16 are a single cluster
  — `chl-*.wvr` (Huawei concurrency challenges): expected `true`, bitvector reports
  `false(no-overflow)`, i.e. a **spurious overflow** the integer encoding does not see
  (`chl-collitem/exp-term/file-item/simpl-str/time-{subst,symm,trans}`, + `linear_interpolation_2`).
  The other 2 are the reverse — `stroeder{1,2}-alloca-1` (expected false), bitvector says
  `true`, a **missed** overflow. So bitvector no-overflow both over- and under-alarms on
  specific shapes; the `chl-*` spurious-overflow cluster is the clear actionable bug.
- **valid-memsafety: bitvector nets positive** — introduces 10 new wrongs but fixes 14.
- **unreach-call: 4 fixed, 1 new. no-data-race: 1 fixed.**
- Plus symmetric 17 wrong→error / 17 error→wrong flips (each encoding finds a spurious cex
  where the other times out).

**Actionable (deferred, do not fix yet):** the `chl-*.wvr` no-overflow spurious-overflow cluster
is the largest single bitvector-encoding wrong — likely a signed/unsigned or width issue in the
bitvector overflow predicate for these concurrency tasks. Worth a focused diagnosis before any
decision to ship bitvector for no-overflow. Integer remains the better default overall
(more correct, fewer wrong, far fewer timeouts).

## Run 2026-07-21_13-24-sanity55 (sosy, 5750G, batches 51-55) — targeted sanity suite, clean

Not a full run: 619 runs over nine folders chosen to cover what batches 51-55 changed plus the
neighbourhoods where the existing wrong results live, so a regression would surface as a *new*
wrong rather than being invisible. Compared per task+property against
`results-2026-07-20_22-41-batch51`.

**Correct 128 → 130. Error 469 → 473. Wrong 17 → 11 (−6). Newly wrong: none.**

- **(a) All six multi-dimensional-VLA false alarms are gone.** `array-patterns/array{13,15,27,28,30}`
  and `array-multidimensional/init-non-constant-2-n-u` all moved from `false(unreach-call)` on
  safe programs to **TIMEOUT**. Worth stating plainly: I expected `Safe`, and that is *not* what
  happened. The unsound aliasing that manufactured the counterexample is gone, so the answer is no
  longer wrong (−16 → 0 apiece, so ≈ +96), but the analysis still cannot decide these within 5 min.
  Soundness restored, capability not gained.
- **(b) All three `(Bv 8)` regressions are correct again** (two `dib3000mc`, one `max8649`), which
  is the `case "char"` fix confirmed end to end.
- **(c) Zero newly wrong**, and that is the load-bearing check for batch 55: it changed how *every*
  array of structs is addressed. The struct-heavy controls genuinely ran — `aws-c-common` 353 runs,
  `ldv-regression` 107, `ntdrivers-simplified`, `heap-manipulation`, `list-properties` — and none
  produced a new wrong or a new frontend failure.

The only other movement is resource noise, and symmetric: two `ntdrivers-simplified` no-overflow
tasks slipped to `TIMEOUT (false(no-overflow))` — the right answer, found too late — while a third
in the same family came back the other way.

Method note: the first comparison keyed on `runset|task|property` and silently matched only 524 of
619 runs, because this suite's run definitions are named differently from `theta27-short.xml`'s.
Keyed on task+property it matches all 619. A join that quietly drops a fifth of the rows is exactly
the kind of thing that hides a regression, so the key has to be checked, not assumed.

**Not covered by this run:** batch 56 (union slicing), which landed after it started.

## Batch 59 — gate off float union punning: `fpToIEEEBV(NaN)` is unsound (fixes the batch-58 regression)

The batch-58 run (below) unlocked the float union idiom and produced **14 wrong `float-newlib`
results** -- a real soundness regression, caught at scale, that the batch-58 module tests missed
because they used only finite values.

**Root cause: `fpToIEEEBV` is unspecified for NaN.** The solver may then read a NaN's bits as any
32/64-bit value, so `value = NaN; word = <bits>; value = word` -- the pervasive newlib idiom, and
these benchmarks are *entirely* about NaN handling ("shall return NaN if the argument is NaN") --
can turn a NaN into a normal float and defeat the `x != x` test. `float_req_bl_0310` (expected
Safe) came back Unsafe on exactly this.

A canonical-NaN guard on the write (`ite(isNaN(x), 0x7FC00000, fpToIEEEBV(x))`, so no `fpToIEEEBV`
is ever applied to a NaN) fixes every direct case -- write-NaN-read-value, write-NaN-read-word,
word-round-trip-read-value all verify Safe -- but the *full* round-trip through a symbolic
canonicalised cell (`value = NaN; word = u.word; u.word = word; value = u.value`) still yields a
spurious non-NaN. That is a deeper FP<->BV abstraction interaction, not closed by the guard.

So float unions are **refused again** (ERROR, score 0) rather than answered wrongly -- the same
"fail loudly" call as batch 45's initializer guard, which the run history keeps vindicating. The
gate is one line in `CStruct.unionCellWidth` (reject a `CReal` member); the read/write machinery and
the guard stay in place, documented, as the starting point for a sound implementation. The core
primitive (`FpToIeeeBv`/`FpFromIeeeBv`, `b683bb605`) is unaffected -- it is correct; only the union
*wiring* over NaN is not.

Result: the 14 float-newlib tasks return to ERROR, so the sound branch is **wrong ~27, down from
batch-51's 34** (the 7 real fixes -- 6 multi-dim VLAs + a bitfield task, now timeouts -- remain).
The batch-56 integer union slicing and everything else stays. Gate: 990 module tests, 255 canaries,
20 fixtures.

## Run 2026-07-21_16-23-batch58 (sosy, **E3-1230 cluster**, batches 51-58) — big frontend wins, and a 14-task FP regression

First full run covering all of this session's work (batches 51-58), on the **E3-1230 v5** cluster
(`--vcloudCPUModel 1230`), which is slower than the usual 5750G -- so cputimes are not comparable and
some solved tasks now time out. Compared per task+property against `results-2026-07-20_22-41-batch51`.

**Correct 10,308 -> 10,257. Error 25,820 -> 25,863. Wrong 34 -> 41.**

The frontend clusters moved exactly as the batches intended (these are CPU-independent):

| frontend-failure cluster | batch51 | batch58 |
|---|---:|---:|
| total frontend-failed | 6,544 | **5,617** (-927) |
| "high dimsension array" init (batch 57) | 865 | **0** |
| "No suitable width found" / (Bv 8) (batch 54) | 217 | **0** |
| union "do not all share a representation" (batches 56/58) | 1,257 | **784** |

The **correct drop (-51) is the slower CPU, not a regression**: correct->error is 51 timeout + 58
OOM + 24 other, against 84 error->correct -- the timeout/OOM churn is symmetric boundary noise that a
slower machine makes worse, and the frontend unlocks still net positive underneath it.

**Wrong 34 -> 41 (+7)** decomposes into **14 newly wrong, all `float-newlib`** (batch-58 FP punning,
`ERROR -> false/true`, one-directional, deterministic -- the soundness bug) and **7 fixed** (the 6
multi-dim-VLA false alarms + `test-bitfields-2-2`, now timeouts). The 14 are addressed by batch 59
above (gated back to ERROR). No *other* newly-wrong task anywhere -- batches 55/56/57's core
memory-addressing changes introduced zero wrong results across the struct/union-heavy families.

## Batch 58 (AD7) — floating-point union punning (unlocks ~265 float-newlib tasks)

The other half of the union work, and the last big union cluster after batch 56. A union of a
double and an integer view -- `union { double value; struct { uint32_t lsw, msw; } parts; }`,
the newlib "extract the exponent/mantissa words" idiom, ~265 tasks -- was refused because a
double's SMT sort is not a bitvector, so reading it as bits needs a *reinterpretation* the model
lacked.

Built in two layers. First the primitive (committed separately as `b683bb605`): `FpToIeeeBvExpr` /
`FpFromIeeeBvExpr`, the raw IEEE-754 bit reinterpretation (`fpToIEEEBV` / 2-arg `mkFPToFP`), as
opposed to `FpToBvExpr`'s numeric rounding. Verified against the JVM's own `Double.doubleToLongBits`
in the constant folder and through a real z3-legacy solve. Wired into every solver backend: z3,
z3-legacy, and JavaSMT natively; the generic SMT-LIB backend throws (`fp.to_ieee_bv` is Z3-only,
and the portfolio uses Z3); Eldarica already has no FP support.

Then the frontend. A float member now contributes to `unionCellWidth` as its encoding width, and
because a float forces bitvector arithmetic the shared cell is always a bitvector. Reading the float
is `FromIeeeBv(cell)`; an assignment is marked so the read-modify-write path splices `ToIeeeBv` of
the value instead of an integer cast. One subtlety the reverse direction exposed: a packed-struct
member that fills the whole cell (`parts`) must return the cell's `Dereference` directly, not a
`sliceOf` wrapper -- a nested write `u.parts.msw = x` needs a real cell to slice, and an
Ite/arithmetic expression is not one.

Verified end to end, both directions and non-vacuously: `u.value = 1.0` gives `u.parts.msw ==
0x3FF00000` and `lsw == 0` (Safe; Unsafe when the constant is falsified), and assembling
`msw = 0x40000000, lsw = 0` gives `u.value == 2.0` (Safe). Three real `float-newlib` `.c` files that
were frontend-rejected now build.

**Still refused, and this is now the last union boundary:** an **array** member
(`union { double value; unsigned char bytes[8]; }`) is many cells, not one word -- the
intel-tdx-module buffer views (764 tasks), which need the byte-addressed layout `ObjectLayout`
computes but nothing yet addresses memory through.

Gate: 992 module tests (core 675 incl. the IEEE eval + z3 solve tests, c2xcfa 180, frontend 137;
new FP-union tests replace the two that asserted the old rejection), 255 canaries, 21 fixtures.

## Batch 57 — multi-dimensional and nested brace initializers (unlocks 865 tasks)

A global multi-dimensional array *with an initializer* was refused outright ("Not handling init
expression of high dimsension array") -- 865 tasks, almost all neural-network weight matrices
(537) and hardness (306). Two things were actually broken, both fixed here.

**The frontend could not build nested initializers at all.** `DeclarationVisitor` called
`initializer.assignmentExpression()` on every element unconditionally, so a nested brace
(`{{1,2,3},{4,5,6}}`, a `bracedPrimaryExpression` rather than an assignment expression) NPE'd and
the *whole* initializer was dropped as `UnsupportedInitializer`. It now recurses: a scalar element
folds to its value, a braced element builds a nested `CInitializerList` of its own.

**c2xcfa now writes the initializer into the flat contiguous cells.** A multi-dimensional array is
one object (batch 49/55), so its initializer has to fill `arrays[a][0..N]` directly; recursing per
row -- the one-dimensional path -- would give each row a base of its own and initialise storage no
read ever looks at, leaving the array silently zero. `initializeFlatArray` walks the initializer
with a single running cursor, the "current object" of C's rules, so both spellings come out
identical: `{{1,2,3},{4,5,6}}` and the brace-elided `{1,2,3,4,5,6}` both fill cells 0..5, and a
short row `{{1,2},{4}}` zero-fills the rest of its row. The key subtlety: the frontend stamps every
element with its per-level position, but for a *descending* scalar that index is not a cell offset
(element k of `int[2][3]` is row k, three cells wide), so the scalar branch follows the running
cursor and ignores it.

Verified structurally (the exact cells 1..6, and 1,2,0,4,0,0 for the short-row case) and
semantically: `a[0][0]+a[1][2]==7` proves Safe, `a[1][0]==4` proves Unsafe, both non-vacuous. Real
hardness `.i` files build again (the neural-network amalgamations progress past this to a separate
pre-existing `__VERIFIER_nondet_float` gap).

**A regression the canaries caught, then fixed:** once nested braces build real lists, a *scalar*
leaf of a deeply nested aggregate arrives wrapped in braces -- the kernel headers write
`{{{{{0U}}}}}` -- and the scalar init branch threw asking a list for its single `.expression`. Three
`ldv-linux-3.4-simple` tasks (`hid-ezkey`, `poulsbo`, `rc-adstech-dvb-t-pci`) went frontend-failed.
`unwrapScalarInitializer` now peels braces down to the scalar (`int x = {{5}}` is 5); an empty or
ambiguous list falls back to the zero value. This is exactly why the 255-canary gate runs on every
frontend change.

Gate: 374 module tests (5 new), 255 canaries, 20 fixtures.

## Batch 56 (AD7, the tractable half) — union members share the word as bit slices

Measured first, then built. Ranking the remaining frontend failures in the batch-51 run put union
punning at the top by a wide margin: **~1,029 tasks** rejected with "Accessing member [X] of a union
whose members do not all share a representation" (`raw` 446, `value` 265, `__theta_anon_0` 207,
`raw_void` 111), against 515 for "Only structs expected here" and 374 for library dereference
offsets. The same ranking showed **217 "No suitable width found for type:"**, which is the `(Bv 8)`
gap batch 54 fixed with one `case "char"` — so that one-liner is worth roughly 217 tasks, not the 3
regressions it was found through.

A union's members all start at offset 0, so a member narrower than the union is simply the **low
bits of the same word**, and `BitfieldSlice` (batch 45) already reads and writes exactly that. So
`union { uint64_t raw; uint32_t half; }` now aliases: the cell is read at the *union's* width and
each member slices it. Assignment needs nothing new -- `sliceOf` stamps the cell as metadata, and
the existing bitfield read-modify-write path splices just the member's bits and leaves its siblings
alone.

Verified semantically, not just structurally: `u.raw = 0; u.half = 7` leaves `u.raw == 7`, and
`u.raw = 2^32 + 1` leaves `u.half == 1`, proving **Safe under both encodings** — and negating that
assertion proves **Unsafe**, so the check is not vacuous.

Two old tests asserted the *opposite* and had to be replaced: `int`/`unsigned` and `int`/`char`
unions were rejected on the grounds that aliasing would lose the sign reinterpretation or the width.
Slicing loses neither -- the read sign-extends from the member's own width, so `u.i = 300; u.c` is
44 -- so those expectations encoded the limitation rather than a requirement.

**What is still refused, honestly.** An **array** member (`union { uint64_t raw; uint8_t bytes[8]; }`)
is many cells rather than one word, and a **floating-point** member has its own SMT sort, so reading
it as bits needs a reinterpretation this model lacks. Those are exactly the two dominant clusters:
`intel-tdx-module` (764, buffer and register-file views) and `float-newlib` (265, the
`union { double value; struct { uint32_t lsw, msw; } parts; }` idiom). Both still want the
byte-addressed object layout, which `ObjectLayout` (batches 52-53) already computes but nothing yet
addresses memory through.

Gate: 369 module tests (4 new, 2 rewritten), 255 canaries, 20 fixtures (union punning in both
encodings).

## Batch 55 — arrays of structs are inline cells too; the 1024 cap is gone

The generic case of batch 54, and it needed a correction to my own reasoning. I had concluded this
was blocked on AD7 because a derived element base `a + i*k` collides with the next object (bases
are handed out three apart). That analysed the wrong design. The right one is what multi-dimensional
scalars already do: **keep the base, put everything in the offset** -- `s[i].f` is
`arrays[s][i*k + f]`, so no base is ever derived and every base stays one the allocator issued.
`deref(1, ...)` and `deref(4, ...)` are different rows of the 2D array and cannot meet. Indexing
past the end lands on cells of the array's own row belonging to no element, which is UB and so
constrains nothing.

Consequences:
- **The `MAX_ELEMENT_ALLOCATIONS = 1024` cap is deleted.** Above it, element bases were left
  unwritten and the solver could equate `a[0]` with `a[1500]` -- the same conflation as the VLA rows,
  just harder to trigger. `struct S a[2000]` now addresses `a[1500].x` as cell 3000, exactly.
- **A plain struct array costs zero allocations**, however long. Only an element containing a nested
  aggregate still needs one per element, written into the element's flat cell.

Three things had to follow the element out of "is an object" into "is a region":
1. `directMemberAccess` folds pointer arithmetic, so `a[i].f` lands on `arrays[a][i*k + f]` rather
   than putting a sum in the base position.
2. `subobjectCell` folds too, which is what makes struct copy, by-value arguments and nested
   subobject allocation work on an element.
3. `t = a[i]` satisfies *both* the pointer-arithmetic rewrite and the struct-copy branch. The copy
   has to win: rewriting it to `t = &a[i]` aliased the two and left `t` a split variable, which then
   failed outright on the next bare use. `a[i] = t` needed a new left-hand-side case for the same
   reason.

Scaling is by **cells, not elements** -- a row of `struct S a[2][3]` with a two-cell `S` is six
cells wide, so `a[1][2].y` is cell 11. Scaling by the element count would have put row 1 inside
row 0; the first implementation did exactly that and the test caught it.

Gate: 359 module tests (6 new), 255 canaries, 18 fixtures. Verified against a stashed baseline that
`a[i] = t` and `t = a[i]` both worked before and still do, and that the one probe that still fails
(`p = q + i` on a split pointer) fails identically without this change.

## Batch 54 — multi-dimensional VLAs address flatly; `(Bv 8)` fixed

Fixes both regressions the batch-51 run found.

**1. Multi-dimensional VLAs (the 6 false alarms).** `rowOf` required the row length to be a
compile-time *literal*. Nothing about the flat model needs that — `i * n + j` is as good an offset
when `n` is a variable — but the literal check sent every VLA down the fallback path, where `a[i]`
became a **stored base** read out of cell `i`. Nothing ever writes those bases, so the solver could
pick the same one for two rows; rows aliased, a summation loop read back the wrong values, and five
`array-patterns` tasks plus `init-non-constant-2-n-u` reported a safe program unsafe.

`arrayLengthExpr` now returns the bound *expression*, literal or not. Verified by dumping the
lowered accesses: `int a[n][n]` with a nondeterministic `n` gives
`base=main::array, offset=(mod ARR_SIZE 2^64)` for `a[1][0]` and `offset=0` for `a[0][0]` — one
object, arithmetic offsets, no stored row bases anywhere.

The regression test pins the *structural* signature rather than a verdict: no write may be
addressed through a base that is itself a dereference, since that is exactly what a stored row base
looks like. Reverting the fix makes it fail.

**Why not the same treatment for arrays of structs** (the >1024 cap, which has the same conflation
defect): `AllocaFunctionPass` bumps the base counter by **3** per allocation regardless of the size
argument (the 3k+1 residue class), and `size` only records bounds for memsafety. So a derived
element base `a + i*k` would collide with the next object's base as soon as `i*k >= 3`. Derived
bases need the allocator to reserve size-proportional ranges first — that is AD7 step 3, not a
patch. Note the multi-dim fix is unaffected by this: it keeps `base = a` and puts everything in the
*offset*, deriving no bases at all. Evidence that deferring is safe: none of the 34 wrong results
in the batch-51 run is a large-struct-array task, so the cap currently costs nothing measurable —
whereas *rejecting* above the cap would turn working tasks into errors for no gain.

**2. `No suitable width found for type: (Bv 8)`.** `CComplexType.getType` matches a bitvector's
width against the architecture's type-size table and switches on the name — but had **no
`case "char"`**, and `char` is the first entry whose width is 8. Every 8-bit bitvector therefore
fell out of the switch and threw, with no bitfield or initializer needed to trigger it. This is the
gap batch 51 documented and worked around; it also explains the three `ldv-linux-3.4-simple` tasks
(two `dib3000mc`, one `max8649`) that regressed correct → frontend-failed when a portfolio
configuration reached it. One `case "char"` fixes it, and `unsigned char` bitfields now build under
bitvector both with and without initializers.

Gate: 359 module tests (3 new), 255 canaries, 18 fixtures (1 new, `char_bitfield_bitvector.c`), and
all six formerly-wrong tasks build. **Not verified locally: the six verdicts flipping to Safe** —
the portfolio needs SV-COMP's 900 s on faster hardware than this host, so what is shown here is
that the aliasing *mechanism* is gone, not the final answers. The next run confirms them.

## Batch 53 (AD7 step 2) — `packed`/`aligned` and unnamed bitfields reach the layout

Batch 52 left two documented gaps, both prerequisites for wiring. Both are closed.

**Layout attributes.** The grammar had always *matched* GCC attributes and thrown them away
("they describe layout, which is not modeled"). `LayoutAttributes` now reads the only two that
change offsets — `packed` and `aligned(n)` — and they reach `ObjectLayout` through `CStruct`.
Everything else stays ignored, as before. Three spellings had to be handled, because they land in
three different places in the grammar:

| form | where it attaches |
|---|---|
| `struct __attribute__((packed)) S { … };` | the struct specifier — the only one `visitCompoundDefinition` sees |
| `struct S { … } __attribute__((packed));` | a **sibling declaration specifier**, after the body |
| `int b __attribute__((aligned(8)));` | a **declarator extension**, after the declarator |

The middle one is what real code overwhelmingly writes, and it was the reason four of the eight
end-to-end tests initially returned the plain unattributed layout. It is applied only when the
specifier list actually *defines* a compound: an attribute on a variable of an existing type
(`struct S x __attribute__((aligned(16)));`) describes the variable, and must not change the layout
every other user of `struct S` sees. `aligned(n)` on a member outranks its struct's `packed`, as in
GCC. A non-literal argument (a `sizeof`, an unexpanded macro) is skipped rather than guessed —
a wrong alignment misplaces every later member, so the natural layout is the safer fallback.

**Unnamed bitfields.** `int : 3;` and `int : 0;` used to be dropped at `visitStructDeclaratorConstant`
and never reached a field list. They still get **no field** — nothing can name them, and giving one a
storage cell would shift every following member in the wired cell model — but they now come back as
nameless declarations and are recorded as `CStruct.Padding`, which `ObjectLayout` replays in
declaration order. `int : 0;` closing the current storage unit is the whole point of the idiom.

gcc caught a rule I would have got wrong: an **unnamed** bitfield contributes no alignment.
`struct {char a; int :3; char b;}` is align **1**, size 3 — not align 4 — whereas a *named* `int`
bitfield does make its struct 4-aligned. Isolating that needed a struct whose named members are all
`char`, which is exactly the kind of case hand-derivation misses.

Gate: 8 new end-to-end tests parsing real C (`ObjectLayoutFromSourceTest`, both data models, all
gcc-generated, including an unattributed control so the plumbing cannot pass by applying `packed`
everywhere), 356 module tests, 255 canaries, 17 fixtures (1 new). This batch touches **wired**
frontend code — the specifier walk and the declarator visitor — unlike batch 52, so the canary run
is load-bearing here rather than a formality.

## Batch 52 (AD7 step 1) — the byte-exact object layout, pure and unwired

`ObjectLayout` computes where every member of a struct/union/array actually sits: bit offsets,
sizes, alignments, per architecture. This is the foundation AD7 needs — the model in which a union
member and its sibling name the same bits, and a `char[16]` view of a struct sees that struct's
bytes. It is the same de-risking shape as `BitfieldLayout` (batch 43-design): **pure, unwired,
independently tested**, so the risky half (rewiring member access onto it) has a checked base.

Implements the System V rules: a member starts at the next offset satisfying its alignment, a
struct's alignment is its strictest member's, its size rounds up to that alignment (so arrays stay
aligned), a union's members all start at zero, bitfields pack into storage units of their base type
and restart rather than straddle one.

**Every expectation is generated by gcc, not reasoned out** — the fixture structs were compiled at
`-m32` and `-m64` and their `sizeof`/`_Alignof`/`offsetof` printed. This immediately paid for
itself on the i386 quirk that an 8-byte `long long`/`double` aligns to **4**, not 8: `struct {char
a; long long b;}` is 12 bytes on ILP32 and 16 on LP64. A hand-derived "alignment == size" rule gets
that wrong, and a negative check (forcing the cap to 64) confirms three tests catch it.

11 tests, both data models. Two honest gaps, both recorded in the class doc:
- **`packed`/`aligned` are not populated.** The class takes them as `Attributes`, but the grammar
  matches GCC attributes and discards them (`C.g4`: "they describe layout, which is not modeled").
  Retaining them through `TypeVisitor` is a prerequisite for AD7's full spec; until then a packed
  struct would be laid out unpacked, so the wiring step must not be enabled for translation units
  whose structs carry layout attributes.
- **Unnamed bitfields are dropped** before reaching the field list (they are padding, no field
  slot), so `int : 0;` cannot currently force the next member into a fresh unit.

Next: the wiring decision — how a program addresses this layout. That is where the risk is, and it
should not start until the batch-51 run has validated the current base.

## Batch 51 — brace initializers splice into their packed bitfield units (fixes the batch-46 regression)

The batch-46 run's 36 newly-frontend-failed tasks, all one guard: once batch 45 packed bitfields
into shared units, a brace initializer's elements — which index *members* — stopped mapping onto
cells, and `initializeGlobalVariable` refused rather than mis-initialize. Each unit's cell is now
folded from its members' initializers at their bit offsets via `BitfieldSlice.write` (the splice an
assignment to a bitfield already used) and assigned once; omitted members keep the zero they fold
onto. A unit holding a single ordinary member keeps the recursive path, so nested structs and
arrays still initialize element-wise.

Verified against a **rebuilt baseline jar with the fix stashed**, which isolated a confounder worth
recording: `unsigned char` bitfields fail under bitvector with "No suitable width found for type:
(Bv 8)" *with no initializer present at all*, so that gap is pre-existing and untouched here. The
bitvector fixture uses word-width bitfields deliberately, or it would pin the wrong bug.

Gate: 152 c2xcfa tests (3 new, value-pinning — `{1,2}` over two 4-bit fields must store 33, not two
cells), 255 canaries, 16 fixtures (2 new, one per encoding), and the three real `test-bitfields-3*`
files plus an `ldv-linux` driver from the regressed cluster all build again.

## Batch 50 — sub-word overlay: any integer members packed into one word

Generalises batch 46 from "a struct of bitfields" to **any struct of integers that fits a machine
word**, which covers the second TDX overlay shape:

```c
union { uint64_t raw; struct { uint32_t lo; uint32_t hi; }; };   // now supported
union { uint64_t raw; struct { uint64_t leaf:16; ...; }; };      // batch 46
```

`CStruct.overlayWidth()` adds up its members' widths -- a bitfield contributes its declared width,
a whole member its type's -- and `overlaySlotOf` gives each its bit range. A nested struct
contributes its own overlay width when it is itself one packed word, since the headers nest
anonymous bitfield groups. Members that are stored as a base id (pointer, array, non-overlayable
struct) disqualify it, as does a total over 64 bits. `sameRepresentation` then compares that width
against the sibling integer, and the access path reads the union's cell at the word's width and
slices it, reusing the batch-45 read-modify-write for assignment.

One thing the wider case needed: the slice comes back in the *cell's* width, so a member narrower
than the word (`lo` in a 64-bit cell) is cast down to its own type -- otherwise every later use
compares a 64-bit value against a 32-bit one, which the bitvector encoding rejects outright.

**Verified in both encodings:** `u.raw = 0; u.lo = 7; u.hi = 3` reads back `lo == 7`, `hi == 3`,
`raw == 7 + (3<<32)`, and a write through `raw` is visible in `lo`. The batch-46 bitfield overlay
still passes; `int`/`unsigned`, `int`/`char` and an over-wide struct still reject.
`UnionPunningTest` (6), module tests, 255 canaries and 14 fixtures green.

**TDX is still not unlocked, and sub-word packing is not what stands in the way.** Instrumenting
the rejection showed the remaining unions are ones no machine word can hold:
`union { uint8_t apic[0x400]; ... uint8_t raw[0x1000]; }` (4 KB buffer views) and a 16×64-bit
register file (`total=1024`) over a `raw` array. Those need byte-level flat layout -- a memory
model where an object is a byte array and every view is a strided reinterpretation -- which is a
different and much larger change than packing members into a word. Both remaining TDX shapes, and
the pre-existing imprecision where a `union` of two arrays lets its views share a base while
reading different per-type arrays, land there.

## Batch 49 — multi-dimensional arrays are one contiguous object (unlocks neural-networks)

Batch 48 gave every aggregate array element an object of its own, which fixed array-of-structs but
was the wrong model for an array *of arrays*: it makes `int a[3][4]` three row objects, so a
`(int (*)[4])` view of a flat buffer — exactly what the neural-network benchmarks cast their
weights to — addresses different storage than the array itself. Rows are now flat instead.

- **Addressing**: `a[i]` on an array of arrays is the region `i * len` elements in, produced as
  plain pointer arithmetic; `dereference` folds that into the offset (`foldPointerArithmetic`), so
  `a[i][j]` lands on `arrays[a][i*len + j]`. The unary `*` already did this folding for `*(p + i)`;
  a subscript needs it too. Object sizes stay keyed on the base expression, which `a + i*len` is
  not — hence the folding rather than a nested dereference.
- **Sizing**: an array's cell count multiplies its dimensions (`flatArraySize`).
- **Allocation**: rows are no longer objects, so nothing is allocated for them; only a *struct*
  element still gets one (a struct's value is its base id). The 1024-element cap therefore applies
  to arrays of structs alone.
- **Index widths**: a row offset is pointer-wide while the subscript beside it is an `int`, so the
  folded operands are cast to the index type first — without that the bitvector encoding refused
  to unify `(Bv 64)` with `(Bv 32)` (integer arithmetic hid it, since every integer is one `Int`).

**Result: the neural-networks cluster builds.** All 8 sampled files go from "Non-array expression
used as array" to a complete build (the 441-file cluster's blocker). Verified in **both** encodings:
a declared `int a[3][4]` and an `int (*A)[4]` over it read and write the same cells in both
directions; 2-D round-trips keep rows distinct; array-of-structs elements stay distinct;
pointer-to-array vs array-of-pointers still resolve correctly; VLAs and above-cap arrays build.
`AggregateArrayElementTest` (5), `PointerToArrayTest` (4), module tests, 255 canaries and 14
fixtures green.

Remaining for TDX: the multi-field-struct-over-integer overlay
(`struct { uint32_t lo; uint32_t hi; }` over `uint64_t raw`) — sub-word packing of two plain
members into one word, the last of its three overlay shapes.

## Batch 48 — array elements that are aggregates get objects of their own

Chasing the neural-networks gap turned up something broader: an array whose **elements are
aggregates** holds a base per element, exactly as a struct holds one per field, but those bases
were never allocated. Two consequences, both pre-existing:

- **Multi-dimensional arrays were rejected outright** ("Not handling init expression of high
  dimsension array").
- **Arrays of structs were silently unsound** — `struct S a[3]; a[0].x = 1; a[1].x = 7;` read
  `a[0].x` back as 7, because the element bases were unconstrained and the solver could conflate
  them. A wrong answer, not an error.

**Fix.** `allocateArrayElements` gives each aggregate element an object, reusing the same
subobject machinery structs already use, so `a[i][j]` is `arrays[arrays[a][i]][j]`. The timing
matters: a declared local array gets its own base from the `alloca` the frontend emits *at its
declaration*, so the elements are allocated right after that assignment — allocating them in the
function's init block (the first attempt) wrote the element bases into the array's *old* base and
they were lost when the real one was assigned. An array is not otherwise assignable in C, so this
fires exactly once per array.

Also fixed while here: **dimension order**. `int a[3][4]` was built as 4 arrays of 3 — the
declarator records `[3, 4]` outwards from the identifier, so the *last* dimension is the innermost
and they must be applied back to front. Only multi-dimensional arrays were affected, and they did
not work at all before.

**Scale cap.** One allocation per element does not scale: the benchmarks contain `S a[100000]` and
`S a[1000000]`, and emitting that many statements made three canaries time out in the frontend.
Above 1024 elements the elements keep sharing an unconstrained base — the pre-existing imprecision,
now bounded rather than unbounded. Giving every element a base without naming it one statement at
a time needs the derived-base memory model (AD7); that remains the real fix.

Also made `fixedArraySize` honest: a variable-length array has no constant element count, so it
answers "none" instead of throwing (it is now consulted for every array, not just nested ones).

**Verified in both encodings:** 2-D arrays round-trip and rows stay distinct; array-of-structs
elements stay distinct (the previously wrong case); a pointer to a 2-D array writes through to the
underlying array; VLAs and above-cap arrays still build. `AggregateArrayElementTest` (4) and
`PointerToArrayTest` (4), module tests, 255 canaries and 14 fixtures green.

Neural-networks are still not unlocked: `A[i][j]` on a `float (*A)[4]` parameter needs the *row*
at index i of a pointed-to array, which is pointer arithmetic over aggregate elements rather than
a declared array's own storage.

## Batch 47 — pointer to array: `T (*p)[N]` vs `T *p[N]`

Started as TDX work and found a bigger gap. The TDX "Non-array expression used as array" failures
are **not** union array views — they are `unsigned long long (*dest)[]` subscripted as
`(*dest)[i]`, the same pointer-to-array gap that blocks the 441 neural-networks files
(`float (*A)[4]`).

**Root cause.** The declarator is walked outwards from the identifier, and both forms arrive with
the *same* star and dimension counts — `T *p[N]` and `T (*p)[N]` were indistinguishable, so the
declarator's star was simply dropped (the pointer-wrapping loop in `CDeclaration.getActualType`
was commented out). `p` was then typed as the array itself, `*p` yielded an element, and
subscripting it failed.

**Fix.** What tells the two apart is *when* the star arrives relative to the dimensions: a star
seen while no dimension has been recorded sits inside the parentheses and binds around the array
(`T (*p)[N]` → pointer to array); a star seen after a dimension belongs to the element
(`T *p[N]` → array of pointers). `CDeclaration` now records the two separately and wraps in that
order. A declaration with no dimensions is untouched, so nothing else moves.
Plus: `*p` where p points at an array denotes **the array object**, whose identity is the pointer
value — not a cell read (the rule `p[0]` already used for a pointer to a struct). Without it the
array's first element was handed back as if it were the array's base.

**A regression I caught before committing.** The first attempt applied the declarator star
whenever dimensions were present, without the ordering distinction. It builds, all canaries pass
— and it silently turns every `T *p[N]` into a pointer-to-array: `int *q[2]` went from correct to
**wrong**. Only the hand-written both-forms test caught it. `PointerToArrayTest` now pins both
bindings so it cannot come back.

**Verified in both encodings:** `(*p)[2] = 7` is visible as `a[2]` (aliasing), the pointer-to-array
is self-consistent, and array-of-pointers still resolves correctly. Module tests, 255 canaries and
14 fixtures green.

**TDX effect:** on the 12-file sample the "Non-array" barrier is gone (6 → 0); those files now
join the rest at the *one* remaining shape, a multi-field struct over an integer
(`struct { uint32_t lo; uint32_t hi; }` over `uint64_t raw`). TDX now gates solely on that.
Neural-networks are **not** unlocked by this: they need `A[i]` for i ≠ 0, i.e. striding to the
i-th row, which is 2-D array-object work beyond the `*p` (row 0) case fixed here.

## Batch 46 — union overlay: a packed-bitfield view aliases its integer sibling

Follow-on to batch 45, using the same slicing machinery. `union { struct { uint64_t leaf:16;
version:8; ... }; uint64_t raw; }` — the kernel/TDX register-overlay idiom — was rejected as
"bit-level type punning" because the anonymous struct was stored as a pointer-wide base id while
`raw` is a 64-bit integer.

A struct that is **one packed unit made entirely of bitfields** (`CStruct.isPackedScalar()`)
holds nothing but that unit's integer, so as a union member it is stored *as* that integer:
`sameRepresentation` compares it that way, the member access dereferences the union's cell at the
integer width, and its bitfields become slices of that shared cell. Writing through the bitfield
view is therefore visible through `raw` and vice versa. The batch-45 read-modify-write path is
reused unchanged, so assignments splice only their own bits.

Verified in **both** encodings: `u.raw = 0; u.leaf = 7; u.version = 3` reads back
`leaf == 7`, `version == 3` and `raw == 7 + (3<<16)` — exact aliasing (Safe). `UnionPunningTest`
now pins the overlay case *and* that the unsound shapes still reject. Module tests, 255 canaries
and 14 fixtures green.

**Scope — this does not unlock the TDX cluster on its own.** Those files carry three overlay
shapes; this fixes one. On a 12-file TDX sample, 6 cleared the punning barrier (and then hit the
next one), 6 still reject. The two remaining shapes both need genuine sub-word flat layout (AD7),
and are deliberately left failing loudly rather than aliased unsoundly:
- **multi-field struct over an integer** — `struct { uint32_t lo; uint32_t hi; }` over `uint64_t
  raw` (two plain members packed into one word);
- **array views** — `union { uint64_t qwords[2]; uint32_t dwords[4]; uint8_t bytes[16]; }`,
  which is what the 6 cleared files hit next ("Non-array expression used as array").

So the 865-run `memberOffset` cluster will not drop much from this alone; AD7 remains its
gating item.

## Batch 45 — packed bitfields: storage units + bit slicing (fixes a memsafety WRONG)

The deferred core-model work, greenlit and landed. Root cause recap: `sizeof` counted one cell
per member (4 for `struct A { char a; char b:2; char c:2; char d:4; }`) while the program
allocates the packed byte size (`malloc(2)`), so member `d` at cell 3 looked out of bounds —
a false `valid-deref`.

- **Layout** (batch 43-design step 1, already landed): `BitfieldLayout` packs a run of bitfields
  into one unit while they fit the base width. Refined here to also require the *same base
  width* per unit — the shared cell is dereferenced at one SMT sort, so `int a:4; char b:4;`
  must not share a unit or the two would land in different per-type arrays and fail to alias.
- **Slicing** (`BitfieldSlice`): a bitfield's value is a slice of its cell. One helper serves
  both encodings — bitvector via `Extract`/`Concat` (inherently logical), integer via
  `/2^o mod 2^w` and place-and-recombine. Signed fields sign-extend from the field width.
- **Wiring**: `CStruct` carries the per-member `Slot`s and `unitCount` (fed the bitfield widths
  by `Struct.getActualType`); `memberOffset` returns the unit index; `directMemberAccess`
  returns the sliced *read* and stamps the cell on it; `FrontendXcfaBuilder` detects that stamp
  on an assignment's left-hand side and **read-modify-writes** just the field's bits. Object
  storage, stack allocation and struct copy now size and index by unit.
- **Containment**: a struct with no bitfields yields `unitIndex == field position` and
  `unitCount == field count`, i.e. byte-for-byte the historical model. Only bitfield-containing
  structs change.
- **Not supported (fails loudly rather than guessing)**: a brace initializer for a struct with
  packed bitfields — elements name members, which no longer map one-to-one onto cells.

**Verification** (both encodings, integer and bitvector): `test-bitfields-1-1` **wrong → correct
(Safe)**; writes to neighbouring bitfields do not clobber each other (Safe); a genuinely
reachable error through a bitfield is still found (Unsafe — not vacuously safe); C truncation
holds (`x.b = 5` into 2 bits reads back 1, leaving `c` intact). Plus `BitfieldSliceTest` (6),
`BitfieldLayoutTest` (6), updated `BitfieldAndAnonymousMemberTest`, module tests, 255 canaries
and 14 fixtures all green. `test-bitfields-1-1` removed from the guard set.

**Still wrong, independent cause:** `test-bitfields-2-2` does `memcpy(p, &d, 4)` — copying a
struct's bytes into a heap buffer, which the cell-based model does not reproduce. That is an
aggregate-`memcpy` gap, not a bitfield one; it stays in the guard set.

## Batch 44 — switch on a wide value with narrow case labels

The union-punning-unlocked aws-c-common files (and others) then died in `CSwitch` lowering with
"(Bv 64) and (Bv 32) can not be unified": `switch (v)` on a `size_t`/pointer-wide value with
`int` case labels compared the controlling expression against each label directly, asking the
core to unify mismatched widths. C converts labels to the controlling expression's promoted
type, so both the case-guard `Eq` and the default-branch `Neq` now compare in the operands'
smallest common type (`switchTestEq`). A `switch` on an `unsigned long` with `int` labels
verifies **Safe**; `SwitchWidthTest` pins the build. Gated: module tests green, 255 canaries +
13 fixtures green. The aws files advance to the next barrier (AD2 split-variable arithmetic).

## Batch 43 — union punning (same-storage members) + `__builtin_object_size`

Two verified wins from the frontend-error frontier.

**Union punning relaxation (the 1,467-run `memberOffset` cluster's dominant idiom).** The
`sameRepresentation` check required identical C *classes*, rejecting `union { void *ptr;
size_t i; }` — the pervasive aws-c-common hash-table idiom — even though a pointer and a
pointer-wide unsigned integer occupy their shared cell identically. Relaxed to: same SMT sort
**and** same width **and** same effective signedness (pointer = unsigned). Width is checked
explicitly because under integer arithmetic every integer is the unbounded `Int` (so `int`/`char`
share a sort but must not alias); signedness likewise keeps `int`/`unsigned` apart, where the
sign reinterpretation would be lost. All 20 sampled cluster files clear the barrier; the
`union { void*; unsigned long }` mini verifies **Safe**; `int`/`unsigned` and `int`/`char`
minis still reject. `UnionPunningTest` pins all three. Sound in **both** encodings — this was
verified against the exact integer-encoding trap the original comment warned about.

**`__builtin_object_size(ptr, type)`** (153-run unresolved-identifier sub-cluster): a
_FORTIFY_SOURCE size query. Grammar rule + visitor returning gcc's size-unknown fallback
(`(size_t)-1` for types 0/1 so the wrapped `__*_chk` never spuriously aborts, `0` for 2/3);
the pointer argument is parsed but not evaluated (no side effects, like sizeof). goblint-coreutils
files clear this barrier (advancing to the next, separate cause — undeclared `malloc`).

Both gated: module tests green, parse canaries 255/255.

### Deferred to a focused pass: bitfield storage units + bit-slice access

The test-bitfields memsafety **wrongs** (`Unsafe(valid-deref)`, confirmed by running
test-bitfields-1-1.i) are NOT a quick fix. Root cause: `sizeof` sums member cells (4 for
`struct A{char a; char b:2; char c:2; char d:4;}`) but the program hard-codes `malloc(2)` for
the packed byte layout, so member `d` at cell-index 3 exceeds the 2-cell object → false
valid-deref. The only sound fix is to *pack* consecutive bitfields into storage units (so the
cell count matches the byte count) **and** *slice* the shared unit on access (so distinct
bitfields don't unsoundly alias). That is a core-model change touching every one-cell-per-field
assumption: `memberOffset`, `structMemberAccess`, and every `type.fields.forEachIndexed` site in
FrontendXcfaBuilder (allocation size 315, stack/heap object storage 319/372/374, 468,
initializeCompound 599/600). Groundwork landed: `CDeclaration.bitfieldWidth` +
`DeclarationVisitor.visitStructDeclaratorConstant` now fold and retain the width. Full design
(storage-unit layout, bv Extract / int div-mod slicing with read-modify-write assignment,
union punning of a bitfield-struct member sharing cell 0) is written below. Held back from an
autonomous commit because a subtle offset error would silently mis-verify *every* struct program
— exactly the bw/int encoding-correctness hazard to avoid landing blind.

## Batch 43-design (bitfield storage units + slicing — full plan for the focused pass)

1. **Layout** — ✅ DONE (pure + tested, unwired): `BitfieldLayout.compute(List<Member>) → Layout`
   (`compound/BitfieldLayout.java`, 6 tests in `BitfieldLayoutTest.kt`). Walks members assigning a
   `unitIndex`: non-bitfield → its own new unit; consecutive bitfields pack into one unit while
   `bitsUsed + width ≤ unitBaseBits`; ordinary member or named 0-width bitfield breaks the run.
   Returns per-member `Slot(unitIndex, bitOffset, width, bitfield)` + `unitCount`. **For structs
   with no bitfields, unitIndex == field position — byte-identical to today, zero blast radius.**
   Remaining wiring (steps 2–7 below) is the deferred, sign-off-gated part: feed CStruct's field
   `(baseBits, bitfieldWidth)` into this, store the Slots on CStruct, and drive memberOffset +
   slicing + RMW assignment from them.
2. **`memberOffset`** returns `unitIndex` (bitfield members in one unit share it). Unit count ≤
   byte size, so the memsafety valid-deref false alarm dies.
3. **Cell iteration**: every `type.fields.forEachIndexed` site in FrontendXcfaBuilder must
   iterate **units** (distinct unitIndex), not members — allocation size = unit count, one
   init/storage cell per unit.
4. **Access** (`structMemberAccess`): a bitfield member becomes an extract of its unit cell —
   bitvector: `Extract(cell, off, off+width)`; integer arithmetic: `(cell / 2^off) mod 2^width`
   — carrying the member cType, plus `bitfieldSlice` metadata `(unitDeref, off, width, signed)`.
5. **Assignment** (`FrontendXcfaBuilder.visit(CAssignment)`): if lValue carries `bitfieldSlice`,
   expand a read-modify-write of the unit cell: `cell := (cell & ~(mask<<off)) | ((v & mask)<<off)`
   (integer analogue with div/mod). Unsigned exact; signed reads sign-extend from `width`.
6. **Union punning of bitfields**: a union member that is a struct-of-bitfields shares the unit
   cell at offset 0 with same-representation siblings — its members become bit slices of cell 0,
   so `raw`/bitfield-view writes alias (the `union { u64 raw; struct { bits }; }` kernel idiom).
7. **Tests**: extend `BitfieldAndAnonymousMemberTest` — read-back after write per field, packed
   `malloc(bytes)` memsafety task verifies Safe, both encodings; a union raw/bitfield punning case.

User-directed immediate sequence before the next full benchmark: (1) test-bitfields memsafety
false alarms, (2) union punning (the 1,467-run AD7 cluster's dominant idiom), (3) nested-brace
initializers. (1) and (2) share one design:

**Diagnosis of the test-bitfields wrongs**: `malloc(2)` records a *byte* size; member offsets
are *field indices*; a packed struct with N>2 bitfield members indexes past 2 → false
`valid-deref`. Packed bitfields are the only case where field index can exceed byte size.

**Design — storage units + bit slices**:
- `DeclarationVisitor.visitStructDeclaratorConstant` folds and retains the width on the
  CDeclaration (unresolvable width → plain field as today).
- CStruct layout groups consecutive bitfield members into *storage units* (one cell per unit,
  unit type = widest base in the run); `memberOffset` returns the unit's index for bitfield
  members. Unit index ≤ byte offset always → the memsafety false-alarm class dies.
- `structMemberAccess` on a bitfield member emits an extract of the unit cell (bv: Extract /
  shift+mask; integer arithmetic: div/mod by powers of two) with the member's cType, and
  attaches `bitfieldSlice` metadata (unit deref, bit offset, width) to the expression.
- `FrontendXcfaBuilder.visit(CAssignment)` checks lValue for `bitfieldSlice` metadata before
  the Dereference branch and expands a read-modify-write of the unit cell:
  `cell := (cell & ~(mask<<off)) | ((v & mask) << off)` (integer arithmetic analogue with
  div/mod). Unsigned bitfields exact; signed reads approximated as unsigned initially.
- **Union punning**: in a union, every member's storage starts at cell 0. A union member that
  is a struct-of-bitfields shares the *unit cell at offset 0* with the other members whose
  representation is that unit (the kernel `union { u64 raw; struct { bits }; }` idiom): its
  members become bit slices of cell 0, so writes through `raw` and reads through the bitfield
  view genuinely alias. The `sameRepresentation` rejection stays for mixed-type unions
  (int/float etc.).

Then (3): nested-brace initializer lists (254 runs) — recurse into braced elements in
`DeclarationVisitor.getDeclarations` instead of the NPE→UnsupportedInitializer fallback,
producing nested CInitializerLists consumed by `initializeCompound`'s recursion.

Status: design written, implementation starting with width retention + storage-unit layout.

## Batch 42 — the TypeUtils.cast cluster: early-typed literals leaking into the decided arithmetic

The 587-run cluster diagnosed (`ldv-linux-3.4-simple`, 217 files). One theme, two expressions:

- **Array dimensions**: struct types registered by the early typedef pass carry dimension
  literals typed for the *default* arithmetic; once the program is decided to be bitvector,
  `getArraySize`'s `castTo` handed an IntType literal to the bitvector CastVisitor →
  ClassCastException. Fixed by extracting the literal's value without any cast and
  re-materializing the memsafety allocation bound via `getValue` (typed for the decided
  arithmetic) — which also de-duplicated the sized/unsized bounds branches.
- **Unknown enums**: `enum kobject_action` with no visible definition fell back to CVoid,
  giving variables a unit-sized SMT sort; any assignment then cast a full-width value into
  `(Bv 1)`. Enum-tagged unknowns now fall back to CSignedInt (a C enum is an int); CVoid
  stays for genuinely opaque types.

After both: sampled cluster files either parse fully or fall through to the catalogued AD2
split-variable rejection. Tests green, parse canaries 255/255.

## Run 2026-07-19_15-36 (sosy, 5750G, batches 38-41) — the verification run

`results-2026-07-19_15-36/`, full 36,602 runs on the LMU vcloud (`--vcloudCPUModel 5750G`,
different hardware than the BME runs; the 2026-07-18 BME run died with the host at ~96%).

**Correct 9,743 → 10,118 (+375). Wrong 98 → 29 (−69). Error 26,381 → 26,090.**

- The 29 wrongs = ~20 documented pre-existing opens (W4 scopes, 2SB/4SB KIND, dijkstra6,
  test22*, 09-regions, CWE121 ×2, lockfree-3.0, memleaks_test11, alloca/strcpy cluster, ...)
  plus 9 error→wrong unlocks, all falling into known gaps: 3 aws `_negated` byte_buf harnesses
  (missed bugs in newly-modeled struct code), `test-bitfields-1-1`/`-2-2` (batch 40's
  bitfield write-width over-approximation misfiring — predicted risk, now measurable),
  scopes3/scopes5/derefInLoop1 (join the W4 lifetime cluster), one hardness sibling.
  **Zero regressions on previously-correct tasks.**
- **ANTLR parse deaths at scale: 4,108 → 2** (`strlcpy.i`/`strlcat.i`, the K&R pair). The
  directive "all parse errors become timeouts/ooms/results" holds to within those two.
- Error mix: pre-parse frontend 4,905 → 4,346 (former ANTLR deaths largely re-land here as
  *clean* rejections — union punning etc. — the rest converted to results/timeouts),
  post-parse 2,536 → 2,603, OOM 2,341 → 2,287, timeouts ~flat, solver 52 → 74.

**Error anatomy of this run**: 19,067 of 26,090 errors (73%) are resource limits — 16,780
timeouts + 2,287 OOM. The 7,023 tool errors (6,949 frontend + 74 solver) cluster by run count:
memberOffset/union-punning 1,467 (AD7); unresolved identifiers 807 (= `__builtin_object_size`
153, library-function *values* `malloc`/`memcpy`/... ~130, forward function references,
atomic builtins, plus casualties of earlier failed declarations); postfix member/bracket/call
visitors ~1,310; `TypeUtils.cast` 587; ReferenceElimination split-variable 719 (AD2);
`FrontendXcfaBuilder` 544; initializer residue (nested braces) 254; CLibraryFunctionsPass 214;
variable-referencing `typeof` 154.

Next levers, in impact order: AD7 flat layout (union punning, 1,467 runs), split-variable
arithmetic (AD2, 719), `TypeUtils.cast` + postfix-visitor diagnosis (~1,900, undiagnosed),
`__builtin_object_size` (153) + library-function values (~130) + nested-brace initializers
(254) as quick wins, bitfield write truncation (fixes the test-bitfields wrongs), W4 scope
lifetimes, K&R definitions (the last 2 parse deaths).

## Batch 41 — struct copies out of cells, and the exponential type expansion

Batch 40's full re-sweep (all 3,173 former parse-death inputs): **888 PARSE-OK (was 777),
2,155 FRONTEND (was 2,316), 110 OOM (was 29), 18 parse-timeout, 2 parse errors (the K&R
pair)**. The OOM growth was batch 40's own doing — structs now keep all their fields, so the
already-exponential `Struct.getActualType` expansion got bigger. Signature ranking of the
2,155: `memberOffset` union-punning rejection ~830 (the kernel `union { u64 raw; struct
bits; }` idiom — sound support needs AD7 flat layout), split-variable pointer arithmetic
(ReferenceElimination, the batch-37/AD2 limit), library-function addresses
(`&malloc`, 38), va_arg locals (30), pointer-to-array indexing (30, Phase-6).

This batch takes the two quick wins:

- **`struct S s = *p;` / `= o.field`** was rejected ("Initializer type not handled for
  structs") — batch 36 allowed only a plain variable (RefExpr) source. A struct value is its
  base id wherever it is read from, so a Dereference source copies identically (aws-c-common's
  `struct aws_array_list tmp = *list_a;`). `StructInitFromDereferenceTest` pins both shapes.
- **`Struct.getActualType` memoization**: the canonical definition's expanded field list is
  now cached (invalidated on `addField`), collapsing the exponential re-expansion. The 317KB
  ums-alauda file that ran 2GB out of heap now finishes in 3.5s; all sampled former-OOM
  files complete (mix of PARSE-OK and ordinary frontend errors).

## Batch 40 — the frontend-crash frontier: struct members that vanished, designated initializers

Follow-up to batch 39's sweep: of the 2,316 files that now get past ANTLR but die in the
frontend, the top signatures were member access on broken structs (171+72 in the partial
count) and "Initializer list designators not yet implemented" (154, all of aws-c-common).

- **One bitfield or anonymous member used to kill the whole struct**: the builder threw
  (`visitStructDeclaratorConstant`: "Not yet supported!"), a caller swallowed it, and the
  struct kept only the fields added before the throw — so *every* later member lookup on it
  failed or mis-resolved, not just the bitfield's. Bitfields are now regular fields of their
  declared base type (member layout is by field index, so this is exact for access; only
  wrap-at-width write semantics is over-approximated). Unnamed bitfields (`int : 3;`,
  BUILD_BUG_ON's `int : -!!(e)`) are padding: no field slot.
- **C11 anonymous struct/union members** get a synthetic `__theta_anon_N` field; member
  lookup flattens through them (`s.a` in `struct S { union { int a; }; }` is two accesses:
  the anonymous member's base, then `a` — the same shape as a named nested struct).
  Union-side punning (`union { u64 raw; struct {bits}; }`, the TDX idiom) still rejects
  cleanly in `memberOffset` — bit-accurate overlay needs AD7-style flat layout.
- **Function-type typedefs** (`typedef void cfs_timer_func_t(ulong_ptr_t);`): the permissive
  name-collecting parse swallows the declared name into the specifiers (the `void
  *malloc(size_t);` shape), so the collector registered the *parameter* name. It now also
  takes the specifiers' last type name when the leftover declarator is a bare `(Identifier)`.
- **Designated initializers** (`{ .field = v, [i] = v }`): the frontend resolves every
  designator to its element position (field index / folded constant; single-level only) and
  stores it in the until-now-unused `CInitializerList` index slot; all four consumers
  (global compound init, unsized-array sizing, local struct + local array lowering) place
  elements by stored position, C-style (a designator sets the slot, each element advances it).
- **Global struct initializer lists** turned out to be unsupported entirely — the global
  CStruct branch asked the list for a single `.expression` (which throws) before dispatching;
  it now routes lists to `initializeCompound`.

Verification: c-frontend/c2xcfa/xcfa tests green incl. new `BitfieldAndAnonymousMemberTest`
(3) and `DesignatedInitializerTest` (4); parse canaries 255/255;
`aws_array_list_back_harness.i` (the designated-init cluster representative) now parses
fully. Full 2,316-file frontend re-sweep pending.

## Batch 39 — ANTLR parse-death elimination: 4,108 task-runs → 3 files

The Jul-16 run had 4,108 task-runs (3,173 unique inputs) die in the parser with
`ParseCancellationException`. Directive: all parse errors must become timeouts/OOMs/results.
Re-measured every input with `--backend NONE` after each wave (sweep tooling: scratchpad
`parse_sweep.sh`, resumable driver; 60s/file, P3).

### 39a — first wave (committed 0eb09a457)

Member/bitfield `__attribute__` positions (~830 tasks), abstract-declarator casts
`(int (*)[8])` (~700), `__typeof` spelling + `typeof(expr)` resolution, `__builtin_offsetof`,
gcc statement expressions. Sweep after: **777 PARSE-OK, 2,316 FRONTEND (past ANTLR, die
later), 34 still-parse-error, 29 OOM (`Struct.getActualType` recursion, 2GB heap), 17
parse-timeout (product-lines simulators + big LDV, just slow)**.

### 39b — second wave (this commit): the 34 → 3

- **Empty initializer `{ }`** (25 files, `rc_map_table lirc[] = { };`): `initializerList?` in
  `bracedPrimaryExpression`; `DeclarationVisitor` emits an empty `CInitializerList`.
- **`typeof(type-name)`** (6 percpu files, `__typeof__(unsigned long)`): typeName alternative
  tried before constantExpression, mirroring sizeof; `TypeVisitor` resolves it directly.
- **The LDV-3.4 chain** (6 files, each fix unmasking the next): attributes between specifier
  and member declarator (`struct kern_ipc_perm __attribute__((aligned(64))) sem_perm;`), bare
  `;` struct members, the `__attribute` spelling (no trailing underscores), attributes after
  the star in a declarator (`void (*__attribute__((section(...))) interrupt[224])(void);`),
  GNU `a ?: b` (elvis; guard reused as the true branch in `FunctionVisitor`), and
  `__builtin_types_compatible_p(typeName, typeName)` (kernel `__must_be_array`; resolved
  structurally where possible, approximated as 0 with a warning where `typeof(local)` cannot
  resolve — 0 is the only value that compiles in the wrapping negative-width-bitfield assert).

**Remaining 3 (deliberately deferred):** `strlcpy.i`/`strlcat.i` (K&R old-style definitions —
`declarationList` is commented out in the grammar, needs visitor merge work) and one lustre
libcfs file (`typedef void cfs_timer_func_t(ulong_ptr_t);` — function-type typedefs are not
registered by `TypedefVisitor`, so the name fails `isTypeName` at use sites).

**Verification:** parse canaries 255/255 after each wave; c-frontend/c2xcfa/xcfa unit tests
green. Next frontier is the FRONTEND cluster ranking (partial, of first ~520): member access
on unresolved types 171 — typedef'd unions of anonymous bitfield structs (TDX idiom), bitfield
members silently dropped from field lists (`visitStructDeclaratorConstant` throws, swallowed
upstream) — designated initializers 154 (aws-c-common), ptr-member access 72,
`CComplexType.getType` 38, `visitPrimaryExpressionId` 30, va_arg 30, ReferenceElimination 29.

## Batch 38 — the 2026-07-16 run's 84 newly-wrong results: four root causes, all fixed

Analyzed `results-2026-07-16_00-35` (base `38705c97a`): 9,743 correct / **98 wrong** / 26,381 error.
Vs the Jul-14 run: +837 correct, but wrong 28 → 98. Log scan attributed every wrong to its producing
config: 60 = `MULTITHREAD_EXPL_COI_SEQ_ITP` *after an OC crash*, 24 = KIND, 9 = `PRED_CART-BW_BIN_ITP`,
2 = `MULTITHREAD_PRED` (missed races), 1 = OC, 2 misc. Four root causes found and fixed:

### 38a — `ReferenceElimination` skipped `main`, so a thread-referenced global's `y*` was never seeded (~60 wrong)

The dominant cluster (58 `pthread-wmm` + goblint/pthread-ext memsafety false `valid-deref`). The pass
early-outs when *this* procedure has no `Reference` labels — but `main`'s only `&` was the
`pthread_create(&t, ...)` handle, already consumed by `CLibraryFunctionsPass`, while the thread
bodies' `&y` obligates **main** (the init procedure) to seed `y* := <base>` + its allocation size,
and main's own `y` accesses to go through the same dereference. Unseeded `y*` made every thread-side
deref check `y* <= 0 || size[y*] <= 0` trivially satisfiable → false alarm from the CEGAR fallback;
main writing plain `y` while threads wrote `__arrays[y*][0]` also split the storage (unsound both
ways). Fix: the early-out now also checks the parent-wide global referred set
(`globalReferredVars`, hoisted into a shared helper). Pinned by `GlobalReferenceSeedingTest`
(no plain `y` writes survive + main and thread write through the same base; fails pre-fix).
`safe000_power.oepc` valid-memsafety: false-Unsafe → **Safe** in 4 s.

### 38b — OC crashed on every memsafety task: `MemsafetyPass` piled parallel label-less `bad → error` edges

`annotateDeref`/`annotateFree` added the `__THETA_bad_deref → errorLoc` (`NopLabel`) edge once **per
annotated dereference**, so the shared bad-deref location had N parallel empty edges — a "branching
location without assumes" that `XcfaToEventGraph` (line 327 `.first()`) died on with
`NoSuchElementException`. Fixed: one shared exit edge per location (added after the loop), and the
OC-side check uses `firstOrNull` so any future shape degrades to the clean `exit("branching with
non-assume labels")`. OC now proves `safe000_power.oepc` memsafety **Safe**; negative control
`mix000.oepc` unreach-call still **Unsafe** (trace 156).

### 38c — the monolithic memory array was split by a syntactic `isGlobal` guess: BMC invented counterexamples (~20 wrong)

`DereferenceToArrayPass` (BOUNDED/monolithic backends only) keyed the `__arrays_*` global on
`(arrayType, offsetType, elemType, isGlobal)` where `isGlobal` was "base is a global var ref, or some
init-edge global assign's RHS == the base expr". A read through global `p1` (RefExpr → `_true` array)
and the write through its constant-folded base literal `2` (`_false` array, the `p1 := (+ 2)` Pos
wrapper defeats the syntactic match) then used **different arrays for the same cell** — reads
unconstrained → KIND/BMC "found" 2-3-step counterexamples on provably safe programs
(`ldv-regression/test07/09/10/16`, `list-properties`, …; also the correct→wrong `test09` no-overflow
regression). Fix: **one array per type triple**, always havoc-initialized — stack/heap garbage
semantics (commit 788eb58c6's intent) are preserved, and global zero-init is already materialized as
explicit writes in the init procedure. All four ldv unreach-call tasks → **Safe** under KIND;
PassTests fixtures updated (`__arrays_Int_Int_Int`, no default-value init).

### 38d — `p[0].f` emitted the p->field double deref through the subscript path (admesh cluster)

`stl->numbers_start[0].number` lowered to `deref(deref(deref(stl,1),0), f)`: the Brackets visitor
read cell `(base,0)` and MemberAccess used that *content* as the object base — W5's `p->field` bug
one production over. Under the struct-value-is-its-base-id model, `p[0]` on a pointer-to-struct IS
the pointee, so the Brackets visitor now returns the pointer itself (wrapped in `Pos` so the struct
`cType` lands on a fresh node, never on the shared `RefExpr` — the known type-corruption trap) for a
**literal-0 index on a CPointer-to-CStruct**; other indices keep the old path (array-of-struct
stride is a separate, documented gap). Pinned in `PtrMemberAccessTest`
(`subscriptZeroMemberAccessEmitsNoNestedDereference`). `admeshFixed`: false-Unsafe → no-verdict at
150 s (the analysis now gets past `initializeStl` and stops at the unmodeled `calloc` — an error,
strictly better than wrong; calloc semantics remain an N1 item).

### Spot-check of all 43 wrong tasks (150 s local budget vs the run's 300 s)

After 38a-c: 14 correct (was 0 among these), 8 no-verdict, 21 still wrong. The still-wrong set is
almost entirely **pre-existing** (wrong or error in the Jul-14 run too) and already documented:
- missed bugs `memsafety-ext3/{scopes1,getNumbers1-1}`, `memsafety/cmp-freed-ptr` (W4 scope
  lifetimes, AD2 architectural), `memory-model/{2SB,4SB}` (KIND false-negative),
  `dijkstra6-both-nt`, `test22-2`, `09-regions_03-list2_rc` (missed race, MULTITHREAD_PRED);
- false alarms `lockfree-3.0`, `test22-1`, `memleaks_test11`, Juliet CWE121 ×2 (undiagnosed,
  pre-existing PRED_CART/KIND memsafety cluster), `scopes4-1` (**diagnosed**: `return arr + 1`
  carries a mid-object pointer across a call — the documented base/offset-across-calls model gap,
  same family as the alloca/strcpy precision cluster), `04-mutex_17` (OC wrong-false, W6),
  `hardness_wrappers_wrapper_ap_file-62`, `dirname-1`, `sll_nondet_insert-2` (all three were
  frontend-error in Jul-14 — unlocked-into-wrong, not regressions).

## Batch 37 — the alloca/strcpy `valid-deref` false-alarm cluster: a scalar copied through split pointers was mis-lowered

The 2026-07-16 run's `alloca`/`strcpy` cluster (`array-memsafety/openbsd_c{st,str}{p,}cpy-alloca`,
`termination-memory-alloca/*`, `termination-dietlibc/strcpy_small`,
`termination-recursive-malloc/rec_strcopy_malloc`) — all **`false(valid-deref)`** false alarms. The
user's guess was "we don't model strcpy, so throw"; the reality is these all **define** their own copy
loops (`cstpcpy`, `cstrcpy`, `cstrncmp`) and use modeled `__builtin_alloca` on the `.i`, so they are
fully modeled and BMC finds a **spurious** counterexample. (The `.c` files fail the frontend on bare
`alloca` — the run uses the `.i`, where it is `__builtin_alloca`.)

**Root cause (fixed, `ReferenceElimination.containsSplitRefs`).** A pointer used with arithmetic
(`++from`) is split into `<v>_base`/`<v>_offset`. Storing a *pointer value* to memory must write both
halves to two channels; but `*to = *from` where the value is a `char` stores a *scalar*. It was
misclassified: the split var `from` occurs inside the value `*from` — only as the *address* read
through — and `containsSplitRefs` counted it as a stored pointer. The store was channel-split into two,
one being `arrays[to_offset][…] := arrays[from_offset][…]` — a dereference **through the offset half as
if it were a base**. `MemsafetyPass` then bounds-checked `__theta_ptr_size[from_offset]` = `ptr_size[0]`
= 0 (unallocated) and reported an invalid deref. Fix: a `Dereference` contributes `false` to
`containsSplitRefs` — a split var in a deref's address is the pointer read through (the deref rewriting
folds it to `deref(base, offset)`), never a stored pointer value; the value read is a single cell. The
`*p = q` pointer-store path (value is a bare split-var ref, not a deref) is unchanged. Pinned by
`SplitPointerScalarCopyTest` (no memory write may address the `_offset` half); canary **255/255**.

**Effect (checked on the fixed jar).** The 4 pure-copy tasks (`cstpcpy`/`cstrcpy`, shape
`for(;(*to=*from);++to,++from)`) go wrong → **timeout** (the spurious cex is gone; the general
unbounded-length proof is beyond BMC, so they time out — score 0, not negative). The decidable minimal
repro `cp_fix1` (l==1) verifies **Safe**. Pointer stores (`*pp=q`, array-of-pointers) still correct.

**Two of the seven remain wrong, distinct causes (not fixed):**
**37d — an assignment expression's value was a re-read of the moved destination (FIXED,
`FunctionVisitor.visitAssignmentExpressionAssignmentExpression`).** `while ((*s1++ = *s2++))` tests the
value of the assignment. In C that is the copied `char`; the post-increments run as side effects before
the next sequence point. But `CAssignment.getExpression()` returns the *lValue* `*s1`, and the guard
re-read it **after** `s1++` had moved the pointer — reading uninitialised memory one past the copy — so
the loop ran on and the next iteration read `*s2` out of bounds. Dumping the guard `CStatement` tree
resolved the earlier code-vs-trace confusion: the value node is a `CExpr(*s1)` and the store + both
increments sit in a nested `postStatements` compound, so the value really is a re-read taken after the
increments. Fix: when the assignment has deferred side effects (`postStatements` non-empty), snapshot
its value into a `__theta_assignedvalue*` temp appended to the body — after the store, before the
post-increments — and let that be the compound's value. Plain `a = b` (no side effects) is untouched.
Narrowing that guided it: `while(*s++)` (no parens, plain read guard) and `char c = (*p++ = 0)` (normal
statement) were both already **Safe** — only an assignment *used as a value* re-read. Pinned by
`AssignmentValuePostIncrementTest` (no loop-branch condition dereferences memory). **Canary 255/255,
zero flakes — the assignment-value change does not go deep.** `pi_fix`/`piv` Safe; **`strcpy_small`
wrong → timeout** (spurious cex gone, unbounded proof beyond BMC).

**Still wrong, and NOT this bug (distinct causes, open):** `rec_strcopy_malloc` copies by **recursion**
(`*dest=*source; if(*source) rec(source+1,dest+1)`) with no post-increment — handled by `backend=CEGAR`
(flagged "recursive"), a recursion + memsafety-precision case, unrelated to 37d. `cstrncmp` is
**precision**: the decidable `cmp_real` (fixed lengths) verifies **Safe** on the fixed jar; the real one
with nondeterministic length + count is beyond BMC/k-induction here. Both want their own effort
(recursion support; invariant strength), not a frontend fix.
- `cstrncmp` (`openbsd_cstrncmp-alloca-1`) — a **precision** timeout dressed as Unsafe at scale; the
  decidable version (`cmp_real`, fixed lengths) verifies **Safe**. Needs invariant/k-induction strength,
  not a model fix. (Also uses `*s1++`/`*s2++`, so the post-increment fix above may help it too.)

## Batch 36 — stack objects are allocated at run time (structs + arrays), and array fields deep-copy

The static base for a stack object is **unsound under recursion and concurrency**: a struct's value is
its base id, and that base was a compile-time constant baked into the procedure init, so every
activation of the function reused it. Two threads running the same function, or two recursive frames,
then shared one `arrays[base]` and a write in one was read by the other. Confirmed minimal repro
`mt_struct` (a thread-local `struct T s; s.x = v; assert(s.x == v)`) was **Unsafe** (a false alarm);
`rec_struct` (recursive frames) likewise, and `rec_nested` (nested + recursion) **crashed** (Z3 sort
mismatch). Local *arrays* were already dynamic (compiled to `malloc`), so `mt_array` was already Safe —
the static-base bug was structs (and struct fields) only.

**36a — stack structs allocated from the runtime counter** (`FrontendXcfaBuilder.allocateStackStruct`,
`AllocaFunctionPass`). Replaced the frontend's static `s := ptrCnt-literal` seed with an
`alloca(target, size)` marker, recursively for struct-typed fields; `AllocaFunctionPass` lowers it to
`__malloc += 3; target := __malloc + 1` (residue 3k+1, the same class the old `ptrCnt` used — no
memcleanup-scan change). The pass was **generalized to write into a memory cell** (a nested field's
base lives at `arrays[parent][i]`, a `Dereference`, not a variable) — a one-liner, since
`AssignStmtLabel(Expr, …)` already dispatches Ref-vs-Deref. By-value struct arguments
(`copyStructArgument`) now allocate their per-call temp the same way, so two concurrent calls don't
share the arg object. Globals stay on the compile-time path (`giveStructObjectStorage`): a global is a
single object, a constant base can't alias. Result: `mt_struct`, `mt_two`, `rec_struct` Unsafe→**Safe**,
`rec_nested` crash→**Safe**, negatives (`rec_nested_neg`) still Unsafe. `mt_nested` (nested struct under
threads) stays Unsafe — but that is the **OC** weak-memory backend's double-deref handling (all three go
through `backend=OC`, and the flat cases flip through it), not the allocation, which recursion proves
correct. Test `NestedStructStorageTest` (rewritten: each inner struct is allocated from the counter),
`StructParameterTest` (arg base is a temp var, not a literal).

**36b — stack arrays use `alloca`, not `malloc`+`free`** (`FunctionVisitor.visitBodyDeclaration`). A
local array was a `malloc` (heap, `3k+0`, program must free) plus a scope-exit `free` — the wrong model:
its memory is released at return, not by the program, and the free made a returned block look
double-freed and a loop-body block look leaked. Now it is an `alloca` (`3k+1`, auto-freed, never
freeable). Aliasing was already sound (both are runtime bases), OOB is still caught (size recorded:
`arr_oob` Unsafe, `arr_ok`/`arr_memclean` Safe, `arr_leak` still Unsafe). Test `StackArrayAllocaTest`
(the array's base takes the `+1` alloca residue, not `malloc`'s bare base).

**36c — a struct's array field gets its own storage and is deep-copied**
(`allocateStackArray`/`arrayCopy`). `allocateStackStruct` now allocates array-typed fields too (and, for
an array of structs/arrays, each element), and `structCopy` copies an array field **element by element**
(`arrays[dst_a][k] := arrays[src_a][k]`) instead of assigning the array base — which had aliased the
two structs' arrays. Closes the last gap the batch-35 write-up flagged. Repros: `sarr_copy`/`sarr_alias`
(deep copy, source untouched) Safe, `sarr_neg` (real bug) Unsafe, `sarr_of_struct` (array of structs)
and `sarr_param` (struct-with-array by value) Safe. Test `StructArrayCopyTest`. A flexible array member
(no bound) falls back to a base assignment — the pre-existing limit for a member whose size is omitted.

Each part is its own commit, verified to fail without the fix, canary **255/255** (36c the cleanest run
yet, zero flakes). Remaining same-area gaps: a *local* array of structs still leaves its elements
unallocated (the `FunctionVisitor` alloca sizes the array but does not walk elements — one layer the
struct path reaches but the top-level-array path does not); and a struct field inside malloc'd memory
still needs the object model.

### Benchmark run `2026-07-16_00:35` (base `38705c97a`, = through 36a) — 96 wrong, down from 116

9,083 correct / **96 wrong** / 25,942 error / 380 unknown. The **aws-c-common cluster (11 wrong in the
batch-32 run) is gone** — cleared by the batch-34/35 struct fixes. Of the 96: ~60 are
`pthread-wmm`/concurrency/**OC** (out of scope) plus `memory-model/{2SB,4SB}`; the rest are sequential.
Notable in-scope cluster still open: **~7 `alloca`/`strcpy` `valid-deref` false alarms**
(`array-memsafety/openbsd_cstpcpy-alloca`, `cstrcpy-alloca`, `cstrncmp-alloca`,
`termination-dietlibc/strcpy_small`, `termination-recursive-malloc/rec_strcopy_malloc`) — checked on the
current jar, **not** fixed by the batch-36 alloca work: they are a *memsafety-precision* problem
(proving an unbounded string-copy loop stays within an `alloca(nondet_size)` buffer whose interior
bytes are uninitialised), not an allocation bug. Still-open missed bugs `memsafety-ext3/{scopes1,
getNumbers1-1}`, `memsafety/cmp-freed-ptr` remain (unrelated to structs — no struct in them).

## Batch 35 — the struct model gives every object its own storage: nested fields get a base, assignment and argument-passing copy

Three bugs, all from the same root: **a struct's identity is its base id, and only *declared* struct
variables were ever given one** — so nested fields aliased (35a), assignment re-pointed instead of
copying (35b), and a struct argument was passed by reference (35c). All fixed; all pre-existing,
none OC or `&expr`.

### 35a — a struct-typed *field* had no storage (`FrontendXcfaBuilder.giveStructObjectStorage`)

`s.f` reads `__arrays_T[s][i]`, so a field that is itself a struct holds a base id in turn (`o.in.x`
is `__arrays[__arrays[o][0]][0]`). `ptrCnt` (whose getter self-increments, `3k+1`) seeded only the
top-level variables, leaving every *inner* struct's base **unconstrained** — free for the solver to
pick, including a value already in use:

```c
struct Out o, p;  o.in.x = 1;  p.in.x = 2;   /* distinct objects */
__VERIFIER_assert(o.in.x == 1);              /* -> was Unsafe: o.in and p.in aliased */
```

Unsound in *both* directions: a write through one object surfaces in an unrelated one (false alarm),
and two objects the program keeps apart can be conflated (hides real bugs). The flat control
(`o.y`/`p.y`) was Safe throughout, which is what localised it to the *nested* level. Fix: recurse
through struct-typed fields at init, seeding a fresh base (and, under memsafety, a size) for each.
C has no struct containing itself by value, so the recursion terminates. Unions are left alone —
their members all start at offset 0, so an index-wise walk does not describe their layout.
Pinned by `NestedStructStorageTest` (two objects ⇒ two *distinct* seeds).

### 35b — struct assignment aliased instead of copying (`FrontendXcfaBuilder.structCopy`)

With identity == base id, `b = a` assigned *a's base* to `b`: the two names then denoted one object.

```c
struct T a, b;  a.len = 1;  b = a;  a.len = 2;
__VERIFIER_assert(b.len == 1);   /* -> was Unsafe */
```

Fix: emit a write per field (`arrays[b][i] := arrays[a][i]`) instead of the base assignment, in
`visit(CAssignment)`'s `RefExpr` branch — the one place both the statement form and the copy-init
form (batch 34's `emitInitAssignment`) go through. The copy is **deep**: a struct field is a
subobject, so its contents are copied and the destination keeps the base 35a gave it; copying the
base instead would reintroduce 35a one level down. Dispatch requires the RHS to be *the same*
`CStruct`, so an expression whose `cType` was lost falls back to the old assignment rather than
being walked as if it had fields. Pinned by `StructCopyTest` (both forms; asserts a write per field,
target base ≠ source base).

**Effect.** `salias.c`/`salias2.c` (both forms) Unsafe → **Safe**. The aws cluster that started this:
`aws_byte_cursor_from_array_harness` now verifies **Safe** (correct) — it needs ~5 min, well inside
SV-COMP's 900 s but past a 120 s probe, which is why a short probe reads as "no verdict"; the other two
(`aws_byte_buf_from_array`, `..._empty_array`) went wrong → *timeout*, a strict improvement (wrong scores
negative, timeout zero). Canary 255/255 for both 35a and 35b (the reported ERRORs were load flakes — all
OK re-run sequentially).

**A missed bug recovered.** `ldv-regression/test22-2` (valid-memsafety, expected false) — one of the four
unsound *missed* bugs from batch 32 — is now found (wrong → OK), and it is **35a** that does it (verified
on the nested-only jar): the aliasing hole was hiding the bug, the "hides real bugs" direction. The other
three are unrelated to structs (`scopes1` and `getNumbers1-1` contain no struct at all) and stay open.

Negative controls all hold, i.e. the fixes are not vacuously making things Safe: a real post-copy bug
is still Unsafe (`copy_neg`), a real nested bug is still Unsafe (`nested_neg`), genuine pointer
aliasing still aliases (`copy_ptr`, `struct T *p = &a`), writing the copy leaves the source alone
(`copy_back`), all fields of mixed width come across (`copy_multi`), and the deep copy holds
(`copy_nested`, 3-level `nested_deep`, sibling `nested_sibling`).

### 35c — a struct argument was passed by reference (`FrontendXcfaBuilder.copyStructArgument`)

The third instance of the same root cause. Passing a struct handed the callee *the caller's base*
(`InlineProceduresPass` binds `param := invokeLabel.params[i]`, and for a struct that value is the
base id), so a write to a by-value parameter mutated the caller's object:

```c
void f(struct T t){ t.len = 9; }
struct T a; a.len = 1; f(a);  __VERIFIER_assert(a.len == 1);   /* -> was Unsafe */
```

Fix, in `visit(CCall)`: for each struct-typed argument, allocate a **fresh base literal**, give it
storage (35a) and deep-copy the argument into it (35b), then pass *that* base. No variable is needed
— the object is a base id and its contents live in the global `__arrays_*`, and a by-value struct
parameter is pure `IN` (never copied back out), so nothing reads the base as an lvalue. The prep
labels are prepended to the call edge; `splitIf` in the inline/malloc passes already isolates the
`InvokeLabel`, so the copy simply becomes the edge before it. Unions keep passing the base (their
model has no per-field layout to walk — same exclusion as 35a/35b). Emitted shape for `f(a)` with
`a` at base 1: `arrays[4][i] := arrays[1][i]` then the call binds `t := 4`, and the callee's
`t.len = 9` writes base 4, leaving base 1 (which `main` reads) untouched. Pinned by
`StructParameterTest` (a cross-object field copy per field; zero without the fix).

**Effect.** `param_val` (mutation isolation), `param_deep` (deep, nested field mutation isolated),
and `param_ret` (`f(mk(n))`, passing a returned struct) all **Safe**. Negative `param_neg`
(`g` returns the field, asserted wrong) still **Unsafe**, and `param_in` confirms the value crosses
*in* (`g(a)` sees a's field). Canary **255/255** (the one ERROR was the recurring
`ArraysOfVariableLength2_-read` load flake, OK alone). Struct-return call sites (batch 34's OUT-param
path) are unaffected — verified `ret_struct`/`salias`/`nested`/`copy_*` unchanged.

### Known gaps in the same area (documented, not fixed)

1. **An array field is copied as its base** — `struct S { int a[4]; }; b = a;` shares the elements
   rather than duplicating them. Same shape as 35a one type over: nothing gives an array *field*
   storage of its own to copy into (a local array gets its base from the malloc `FunctionVisitor`
   rewrites it to; a field gets nothing). Strictly better than the pre-fix whole-struct alias, but
   still wrong.
2. ~~A struct *parameter* is passed by reference~~ — **fixed in 35c below.**
3. **A struct field inside malloc'd memory** has the 35a problem with no declaration to hang the
   seed on (`p = malloc(sizeof(struct Out)); p->in.x = 1;`). Needs the object model, not a seed.

## Batch 34 — `struct S s = <expr>;` never copied anything

Chasing the remaining `aws-c-common` `byte_buf`/`byte_cursor` false alarms. Minimal repro is five
lines: `struct T mk(unsigned long n){ struct T t; t.len = n; return t; }` +
`struct T b = mk(n); assert(b.len == n);` → false **Unsafe**. Isolated by controls: asserting *inside*
`mk` is Safe (the write happens), a scalar return is Safe, filling through an out-param is Safe, and
`struct T b; b = a;` (declare **then** assign) is Safe — but `struct T b = a;` (**copy-init at the
declaration**) is Unsafe.

**Cause** (`FunctionVisitor.visitBodyDeclaration`): the struct branch, for a non-initializer-list
initializer, `checkState`d that the expression is a `RefExpr`, that its type is a `CStruct`, and that
the types match — **and then emitted nothing**. Type-checking is not initialising: the variable was
declared and never written, so every field stayed unconstrained and the solver could read whatever it
liked out of it. From the model, pre-fix: `assign c = (ite (= (deref 4 0 Int) main::n) 1 0)` with **no
write to `deref 4 0` anywhere**; post-fix: `(memassign (deref 1 0 Int) mk::n)` is there and the read
sees it. (With the initializer dropped, nothing aliases the callee's struct, so the callee's own write
becomes dead and is removed too — hence *no* write at all.) The statement form always worked, so the
fix emits exactly that, via an `emitInitAssignment` helper now shared with the non-struct branch.

This is the shape every struct-returning function has at its call site — `struct aws_byte_buf buf =
aws_byte_buf_from_array(a, len);` — so the aws harnesses were all asserting on an uninitialised
struct. Pinned by `StructInitTest`. Note the `struct T b = a;` form reaches the same branch but makes
no test that can fail (the source's own write is there either way and the copy *aliases* rather than
adding one), so the call form is what the test uses.

**It is not the whole `byte_buf` story — and the next layer is bigger.** Sweeping the 11 wrong aws
harnesses on this HEAD: **1 OK** (`aws_add_size_saturating`), **3 still wrong**
(`byte_buf_from_array`, `byte_buf_from_empty_array`, `byte_cursor_from_array`), **7 now reach no
verdict** (wrong→error is scoring-neutral-to-better, but not a fix).

### ⚠️ NEXT, AND PRE-EXISTING: struct assignment *aliases* instead of *copying*

Narrowed from the still-wrong harnesses. `struct T b = mk(); rd(&b);` is Unsafe while
`struct T b = mk(); b.len` (direct read) is Safe and `struct T b; b.len=7; rd(&b)` is Safe — i.e. the
copy-init makes `b` **alias** the callee's object rather than copy it. The direct minimal proof:

```c
struct T a, b;  a.len = 1;
b = a;          /* C copies here */
a.len = 2;      /* must not affect b */
__VERIFIER_assert(b.len == 1);   /* -> Theta reports Unsafe */
```

Both `b = a;` and `struct T b = a;` are Unsafe, so this is **not** from batch 34 — the statement form
predates it (that is exactly why `b = a;` "worked" for direct reads and looked like a good path to
reuse). A struct variable holds a base id, and assigning one to another just re-points the base, so
the two names share storage: reads see the source's *later* writes, and `&b` does not see the copy at
all. Wrong C semantics for any program that copies a struct and then touches the source.

Batch 34 is still a strict improvement (uninitialised → aliased, and aliasing is right whenever the
source is not modified afterwards, which is the common case and is why the direct-read repros pass),
but the real fix is to **emit a field-by-field copy** — the initializer-list path already writes
fields as `Dereference(v.ref, i, fieldType)`, and `CStruct` carries the fields, so the shape exists.
It is a genuine change to the struct model's semantics (each struct variable needs its own storage),
so it wants its own careful pass + full canary, not a tail-end patch. **Highest-value next target:
it is a correctness bug in its own right, well beyond aws.**

## Batch 33 — the aws saturating cluster: two independent bugs, one of them an unsoundness that hid real bugs

Chasing the batch-32 `aws-c-common` false alarms turned up **two unrelated bugs**, both fixed; the
`aws_add_size_saturating_harness` needed *both* and is now **OK** (was wrong).

**1. `__builtin_uadd*_overflow` took its width from `res`, not from its own name**
(`ExpressionVisitor.unsignedOverflowBuiltin`). The typed builtins fix their width by name — `uadd` is
`unsigned int`, `uaddl` `unsigned long`, `ll` `unsigned long long` — but the model read it from
`pointer.getEmbeddedType()`, i.e. from `res`. aws-c-common's `aws_add_u32_saturating` writes a 32-bit
`__builtin_uadd_overflow` through an `unsigned long c`, so the addition was carried out in **64 bits,
where two 32-bit operands can never overflow**: the call always answered "no overflow", the saturating
result disagreed with the caller's own `a > UINT32_MAX - b`, and the assertion false-alarmed. Fixed by
passing the builtin's own `CComplexType` per case; the wrapped result is truncated to that width and
then cast to `res`'s type for the store. Pinned by `OverflowBuiltinWidthTest` (the flag is
`overflow := wrapped_sum < a`, so the modulus the sum wraps at *is* the width — asserted 2^32 for
`uadd`, with `uaddl`/2^64 as the control; fails with the fix removed).

**2. ⚠️ Both arms of an `if` shared one scope — an UNSOUNDNESS, not just a false alarm**
(`FunctionVisitor.visitIfStatement`). `visitIfStatement` pushed a single `if<N>` scope and visited
*both* arms inside it, and a brace-enclosed arm does not open a scope of its own (`visitBlockItemList`
only does that for a block nested directly in another block). So a name declared in both arms was **one
variable wearing two C types**: the second declaration found the first in the scope map, reused its
`VarDecl`, and overwrote the recorded `cType`. Every use — in *either* arm — was then typed by whichever
arm was visited last. For `if (c) { uint64_t a; } else { uint32_t a; }` (exactly how aws-c-common writes
its 64/32-bit harness pairs) the 64-bit arm was **narrowed to 32 bits**: `main::if0::a` was assigned
`(mod nondet_ulong 4294967296)`. That is unsound in both directions — a 64-bit value silently stops
being able to exceed 2^32, **hiding real bugs** (minimal repro: a program that reaches an error only
when a 64-bit local exceeds 2^32 was reported **Safe**; now correctly Unsafe), and it corrupts the
arithmetic the other arm asserts about (the aws false alarm). Fixed by giving each arm its own scope
(`inOwnScope("then"/"else", …)`); `if` is the only construct with two sibling arms (`while`/`for`/
`switch` bodies are a single block, so their one scope is right). Pinned by `BranchScopeTest` (fails
with the fix removed). **Checked, and it is NOT the cause of the batch-32 missed bugs** (I suspected it
would be, from the name `scopes1`): after the fix `memsafety-ext3/scopes1` and `memsafety/cmp-freed-ptr`
and `ldv-regression/test22-2` are still `got=true want=false`, and `memsafety-ext3/getNumbers1-1` now
errors. Those four are a separate, still-unexplained soundness hole — do not re-attribute them to
branch scoping.

A first attempt — disambiguating colliding flat names in `createVars` — was **reverted**: it never
fired, because the two arms share the scope *map*, so the second declaration takes the `containsKey`
reuse path rather than creating a fresh (collidable) name. The scope, not the name, was the bug.

**Still open in the aws cluster:** the ~10 `aws_byte_buf_*` / `aws_byte_cursor_*` harnesses remain
wrong — a distinct, unexplored cause (buffer/pointer harnesses, not saturating arithmetic).

## Batch 32 — full post-rebase re-run (`2026-07-15_00-23`, base `6cfbe4bd6`) analyzed; the wrong-count tripled and one root cause explains most of it

Retrieved from `benchcloud:results/Theta-svcomp/theta27-short.xml/2026-07-15_00:23:24` (55 result
XMLs). This run's jar is **`6cfbe4bd6`** — post-rebase but **before** `castTo`/`bvOverflow`/realloc/
initializer-array (all committed 00:39–10:50). Totals: **9659 correct / 116 wrong / 26448 error / 379
unknown**. Correct up, but **wrong jumped 28 → 116** (the wrong count is budget-independent, so this is
real, not the longer timeout). Spot-checking on current HEAD (`349649d4c`) showed only `psyco` is
fixed by the later commits; the rest are genuinely open.

**Wrong split: 66 concurrency/OC (OUT OF SCOPE) + 50 sequential (in scope).** The 58 `pthread-wmm`
`valid-memsafety false(valid-deref)` all come from the **OC backend** (config trace: `backend=OC`
under the `MULTITHREAD` portfolio) — OC is the separate-PR territory we do not touch; flag for its
owner, do not fix here. Plus 2 `no-data-race` and a few other concurrency = 66.

**The #1 in-scope regression, root-caused: a split pointer *parameter* is never bound to its argument
at the call.** ~24 of the 50 sequential wrongs are `valid-memsafety false(valid-deref)` on the
`str*`/`alloca` family (array-memsafety, termination-{memory-alloca,15,dietlibc,recursive-malloc},
ldv-memsafety, busybox, Juliet). All memory-safe; all false alarms; all were **timeout** pre-rebase
(batch 25) → now **wrong**. Minimal 7-line repro (`scratchpad/ms_K.c`):
`char g[4]; int f(const char*s){ while(*s){s++;} return *s; } int main(){ g[0]=0; return f(g); }` →
false `Unsafe valid-deref`. Mechanism, from the serialized memsafety XCFA: because `s++` makes
`ReferenceElimination` split the parameter `s` into `f::s_base`/`f::s_offset`, but the call-site
binding (`f::s = g`, produced by inlining) is **dropped to `skip skip`** instead of being split into
`f::s_base = <g base>; f::s_offset = 0`. The parameter enters `f` **unconstrained**, so the solver
picks an out-of-range `f::s_offset`, walks off the end, and the bound check `size[s_base] > s_offset`
fails. Confirmed against the non-split case: `ms_G` (a `char*` param used only as `*s`, never
incremented, so never split) IS bound (`assign f::s main::a`) and is correctly Safe. So the drop is
specific to the *split* parameter. Fix lives in `ReferenceElimination.changeComplexAssign` /
whatever elides the inlined param binding before the split — the binding must be split, not dropped.
**FIXED (`seedSplitParams` in `ReferenceElimination`).** Pinned with a debug build: there is no
binding to drop — `ReferenceElimination` is at ProcedurePassManager **line 51, before**
`InlineProceduresPass` (line 69), so it processes the callee `f` standalone and splits its *parameter*
`f::s`; inlining then binds the original (now-split-away) `f::s`, and the halves `f::s_base`/
`f::s_offset` are never seeded (the base/offset split is a rebase-era feature — params weren't split
before). Fix: when a split var is an IN parameter, seed `param_base = param; param_offset = 0` at the
procedure entry (offset 0 because the model cannot carry a mid-object pointer across a call — a bare
split variable as an argument is rejected outright, so whatever the caller binds is exactly the base).
`ms_K`/`ms_E`/`ms_M` go Unsafe→**Safe**; the hard two-string `cstr*` tasks go wrong→timeout (both
strict scoring wins over a false alarm). Pinned by `PointerParameterTest` (asserted to fail with the
seed removed). **255-canary: 251/255**, the 4 deltas all `expected=false` bug-finders that pass **OK
run alone** — load-induced flakes under the 75 s + `-j6` budget (my fix makes pointer-param tasks a
touch heavier), not correctness regressions; the real 900 s budget is far more forgiving. No pass-
level crash on any of them (`--backend NONE` builds clean).

**Other in-scope clusters (not yet root-caused):** 11 `aws-c-common` + ~7 other `unreach-call`
false alarms (ldv-regression test07/09/10/16, list-properties, hardness — may share the pointer-param
bug or be their own); and **~5 genuinely unsound missed bugs** (got true/safe on expected-false):
`memsafety/cmp-freed-ptr` (use-after-free), `memsafety-ext3/{getNumbers1-1,scopes1}` (valid-deref),
`ldv-regression/test22-2` (no-overflow). `psyco_math_1` (got-true) is already fixed by `349649d4c`.

## Batch 25 — full re-run (`2026-07-14_13-10`, HEAD `8c58af94e`) analyzed; one soundness regression found

The re-run the previous batches asked for. Limits `300s / 7GB` (vs the batch-8 baseline's `900s / 8GB`),
so vs baseline the time budget is **3× tighter** — every gain below is *despite* that.

| bucket | BASE (07-06, 900s) | PREV (07-13, 300s) | NEW (07-14, 300s) | N−BASE | N−PREV |
|---|--:|--:|--:|--:|--:|
| correct | 5917 | 8356 | **8906** | **+2989** | **+550** |
| wrong | 13 | 28 | 28 | +15 | +0 |
| fe_before | 14539 | 7649 | 7647 | −6892 | −2 |
| fe_after | 2960 | 1324 | 1324 | −1636 | +0 |
| timeout | 10607 | 16827 | 15782 | +5175 | **−1045** |
| oom | 2437 | 1944 | 2433 | −4 | +489 |

PREV and NEW share limits, so **N−PREV isolates the last four commits** (range de-dup `37710db08`,
short-circuit `35dde5041`, for-init grammar `915fb73fa`, plan). They recovered **+550 correct /
−1045 timeout** — the −950 regression is confirmed recovered. (The +489 oom is timeout→oom churn:
643 tasks that used to time out now get far enough to exhaust memory instead; scoring-neutral.)

Correct-by-property vs baseline: no-overflow **+2788** (1200→3988), valid-memsafety **+574**, termination
+23, memcleanup +25, no-data-race +12; unreach-call **−433** (the 900s→300s budget cut costs 987
correct→timeout, only partly offset).

**Wrong count held at 28 but the set churned.** Fixed by the grammar change: the whole
`termination-memory-alloca` cluster left "wrong" (`genady-alloca` no-overflow now **correctly Safe**;
the four valid-memsafety allocas now timeout, not wrong). Newly wrong: the known `aws-c-common` /
harness false-alarm cluster now *completes* (was timeout) instead of newly breaking.

### ⚠️ SOUNDNESS REGRESSION: `psyco/psyco_math_1` (no-overflow), correct → wrong, caused by `35dde5041`

The one genuine `correct → wrong` from the last four commits. Expected verdict **false** (a real signed
overflow at trace length 13). PREV: config `KIND-mathsat` returned `Unsafe Trace length: 13` in 37s.
NEW: the *same config* returns `Safe` in 4s. Reproduced locally, then isolated by reverting each suspect
in a worktree: reverting `37710db08` (range) → still Safe (not it); reverting **`35dde5041` (short-circuit)
→ `Unsafe Trace length: 13`** (correct). **`35dde5041` is the culprit.**

Mechanism (from the `--backend NONE` XCFA, buggy vs `35dde5041`-reverted): the reverted model has **11
overflow-check "error" edges** on `P1 - 1` (`bvadd P1 #b…1`, the `(P1 & (P1-1))` idiom repeated ~10×);
the buggy model has **1**. `35dde5041` lets a *pure* `&&`/`||` operand run unguarded, which leaves its
statements bare; the arithmetic then **folds into the surrounding condition**, where the overflow
instrumentation no longer emits a check — a real overflow silently becomes unreachable ⇒ unsound `Safe`.

**`35dde5041` must not simply be reverted, and neither must `89020cef2`.** `89020cef2` is a genuine
soundness fix (it made `&&`/`||` short-circuit *function calls* — `x!=0 && f()` must not call `f()`
when `x==0`; pinned by fixtures). Reverting `35dde5041` alone re-introduces the −950 timeout mass it
was written to fix (which costs *more* SV-COMP points than the single wrong result saves), so it is a
real trade, not a free win.

**Two fix attempts that did NOT work** (both built and tested against psyco + the file-114/mod3
regressors): (a) re-emitting a pure operand's statements as an unguarded `compoundOf` — the arithmetic
still folds, psyco stays Safe; (b) extending `mustNotRunUnconditionally` to guard operands whose value
`carriesUbCheck` (Add/Sub/Mul/Neg/Div/Mod/ShiftLeft) — file-114 got *more* guarded (8s→42s) but psyco's
operands were **not** caught: their `P1-1` is folded into the operand *value* (always folded into the
`Ite(And(collect),…)`), so guarding the operand's *statements* cannot un-fold it. The real fix lives at
the expression level — PLAN.md l.266 notes `OverflowDetectionPass.getExpressions` already threads a
short-circuit condition through `AndExpr`/`OrExpr` and wraps a guarded expr as `Ite(cond, expr, 0)`;
the folding introduced by `35dde5041` is defeating that threading. ~~Open~~ **RESOLVED in batch 31 —
the guess above was right about *where* (the `Ite(cond, expr, 0)` threading) but wrong about *why*:
the threading works, it was the *bitvector* overflow encoding that could not read through the `Ite`.**

## Batch 31 — the psyco soundness regression, fixed at the real cause: `bvOverflowCondition` couldn't see through the short-circuit `Ite`

The `correct → wrong` from batch 25 (`psyco/psyco_math_1` no-overflow, a real signed overflow on
`P1 - 1` proved `Safe`). Root-caused end to end and fixed in **`BvOverflow.kt`**; `35dde5041` was the
*trigger*, not the bug, and the batch-29 `castTo` fix is **innocent** (the earlier hypothesis that it
stripped the operand's `cType` was wrong — instrumented the debug and the `bvadd` still carries
`cType=CSignedInt`).

**The actual mechanism.** `OverflowDetectionPass.getExpressions` threads each `&&`/`||` operand's
short-circuit guard through and, when it finds a signed arithmetic expr under a non-trivial guard,
adds `Ite(reached, arith, 0)` to the set instead of the bare `arith` (the operand — and its overflow
— is reached only when `reached` holds). The **integer** branch handles this: it range-checks the
whole `Ite` with the limit visitor (the `else` 0 is trivially in range). The **bitvector** branch
(`bvOverflowCondition`) reconstructs the overflow from the *operands* by redoing the op one bit wider
— but the operands sit inside the `Ite`'s `then`, and the function's `when` had no `IteExpr` case, so
it hit `else -> null` and the check was **silently dropped**. `P1 & (P1 - 1)` makes the whole program
bitvector-analysed (the `&`), and the `1 && (… || 0)` psyco wrapping folds `P1 - 1` behind a guard —
so exactly this path, and the overflow at `P1 == INT_MIN` went unreported ⇒ unsound `Safe`. Before
`35dde5041` the pure operand was *guarded into its own statement*, where the arithmetic sat under a
`True` guard and was added bare — hence the pass saw it and it worked; `35dde5041` folds it inline
under a real guard, exposing the latent `Ite` hole.

**The fix (`BvOverflow.kt`):** give `bvOverflowCondition` an `IteExpr` case up front — recurse into
`then` and guard the inner overflow with the condition: `And(cond, bvOverflowCondition(then))`. Sound
(the overflow is asserted only when the operand is reached), minimal, and **touches nothing else** —
`35dde5041` stays (perf preserved), `castTo` untouched, no revert. Verified: `psyco_math_1` now
**`OK` (Unsafe)** through the SV-COMP dist; a minimal `1 && (((a & (a-1)) == 0) || 0)` goes from 0 to
1 overflow-error edge; the integer and plain-bitvector-statement paths are unchanged. Pinned by
`OverflowShortCircuitTest` (c2xcfa) — asserted to **fail** with the `Ite` case removed. **Diagnostic
trap avoided:** `grep __overflow__` on the serialized XCFA is a false metric — the intermediate loc
is only named `__overflow__` when the check is *not* the edge's last label; otherwise it is `__loc_N`.
Count edges to `*_error` instead. This cost one wrong turn (thought overflow detection was broadly
dead) before switching metrics.

## Batch 30 — realloc modeled; an initializer-sized global array; Neutral BvType already gone

- **`realloc` no longer crashes the analysis** (`7a748f8ee`, new `ReallocFunctionPass` after
  `MallocFunctionPass`). It was reaching the LTS as a live `InvokeLabel` -> `error("No such method
  realloc")`. Modeled as an **in-place resize**: `p = realloc(q, n)` keeps `q`'s base and sets the
  object's size to `n`. A program must use realloc's *return value* whether or not the block moved, so
  same-base preserves the observable contents and the new bound -- no havoc (which would false-alarm on
  the copied data), no crash. It does not model invalidation of the *old* pointer (use-after-realloc of
  `q` looks valid), the same imprecision the analysis already has around frees; `realloc(NULL,n)` and
  `realloc(q,0)` are left as the resize too. Verified: contents preserved, grow-then-read Safe.
- **An initializer-sized global array no longer NPEs** (`812d8517d`). `struct command commands[] = {…}`
  has a *null* `arrayDimension`; the memsafety branch of `initializeGlobalVariable` read
  `arrayDimension.expression` directly. Now sized from the initializer via `getArraySize`, exactly as
  the non-global path already did -- `int xs[] = {1,2,3,4,5}` is Safe again. A *nested* aggregate
  initializer (`struct C cs[] = {{…},…}`) still fails, but now as a clean `UnsupportedFrontendElement`
  rather than a raw NPE -- that is the initializer-list item (queue §5), left for its own change.
- **Neutral BvType is already resolved.** `memsafety-ext3/scopes2.c` -- the standing repro for "Neutral
  BvType cannot be used here" -- now returns `Unsafe`; the rebase (or the `castTo` fix, which changed how
  a bitvector literal keeps its signedness through a cast) fixed it. Struck from the queue.

## Batch 29 — the rebase silently disabled unsigned wraparound (root cause of the "canary regression")

The post-rebase canary looked like it had lost ~13 tasks. Most of that was **my harness** (`canary_full.sh`
flagged a CRASH on any exception text, but a portfolio catching a config's failure and recovering is
normal -- fixed to classify on the final verdict). Under it were four real, rebase-introduced bugs, now
fixed, plus one perf regression left open:

1. **`CComplexType.castTo` short-circuit (the root cause), `1769bd2ff`.** cir-frontend added
   `if (getType(expr).equals(this)) return expr;` to `castTo`. But a cast is not a no-op merely because
   the recorded type matches: it is what holds a value in range. `unsigned + unsigned` is *typed*
   unsigned, yet its value stands one past the maximum until the cast's modulo wraps it -- and the
   additive visitor stamps the sum with its result type *before* casting. So the short-circuit skipped
   the wraparound modulo and **`UINT_MAX + 1` stopped coming back to 0** -- every unsigned wraparound
   silently broke (e.g. `cancel_var_through_overflow`). Fixed: skip only when `!isArithmetic(expr)`.
   `CastVisitor.widthPreserving` was likewise tightened to skip the modulo only for a value that cannot
   leave its range (`049b71020`) -- an *arithmetic result* still needs it.
2. **`deepCopy` empty-identifier suffix, `09922ef11`.** `it.copy(name = "${it.name}_$identifier")` with an
   empty identifier made `__THETA_bad_deref` into `__THETA_bad_deref_`, so every memsafety violation found
   by a monolithic backend threw "Could not determine subproperty". Also matched by prefix now in
   `LtlPropertyFromTrace` (`6cfbe4bd6`), since a per-thread copy legitimately yields `__THETA_bad_deref_0`.
3. **`OverflowDetectionPass` bare `StmtLabel`, `48566dabf`.** Its overflow->error edge was a bare
   `StmtLabel` while everything downstream wants a `SequenceLabel` (`splitIf` asserts it); cir-frontend's
   frontend started producing programs that hit that branch, crashing bresenham/nla tasks with no verdict.

Two things I tried and **reverted**, because the root-cause fix subsumed them: stepwise n-ary overflow
checks (`AdditionIntMax` is caught anyway once the arithmetic is no longer folded away, and they cost
performance), and a `SimplifyExprsPass` `inputProperty` guard (it disabled essential loop-constant folding
and timed out `flag_loopdep`; the pre-rebase `verifiedProperty` behavior is right).

**Canary: 142/143.** The remaining task, `recursified_nla-digbench/recursified_geo1-u.c` (no-overflow), is
a **performance regression from cir-frontend's frontend**: 22s pre-rebase, >240s now. Not from these
fixes (they do *fewer* casts than pre-rebase), and **property-independent** -- it also times out as
`unreach-call`, so it is the *base model* cir-frontend now builds for this recursive nonlinear-arithmetic
task, not overflow instrumentation. Likely affects the `recursified_nla-digbench` family broadly; left for
the full-benchmark data to size (a `git bisect` across cir-frontend's history would pin the exact commit).

## Batch 28 — width-preserving casts drop the modulo; a pointer survives a round trip through an integer

**`PassTests[13]` fixed** (`122b74775`). The rebase's one failing test: cir-frontend tightened
`pthread_create` to require a real procedure as the thread entry, and the DSL already had a
`siblingProcedures` hook for exactly that — the case just wasn't using it. `thr1` is now registered as
an (empty) procedure. 28/28.

**A width-preserving cast needs no modulo** (`f87c1976e`, integer `CastVisitor`). A source that can
never be negative -- an `Unsigned` type, or a `CPointer`, whose value is a non-negative object id --
and no wider than the target already lies in the target's range, so `Mod(x, 2^w)` is a no-op. It now
returns `Pos(x)` instead. (A *distinct* `Pos`, not the bare operand: `castTo` records the target type
on whatever it gets back, and stamping it on the operand itself would overwrite that operand's own
recorded type -- the aliasing trap `ArrayIndexTypeTest` guards.) Both directions are covered by the
same six unsigned visits, because `visit(CPointer)` delegates to `getUnsignedLong`.

**A pointer routed through an integer keeps its base and offset** (`d992c8fc4`). With the modulo gone,
`(unsigned long)p` is a `Pos` no-op, so `ReferenceElimination` now looks through `Pos` when it
recognises split-variable copies and dereferences. `int *p = &a[3]; unsigned long q = (unsigned long)p;
int *r = (int *)q; *r = 5;` correctly writes `a[3]` -- the split pointer's *offset* survives the round
trip. Validated: 6/6 `PointerArithmeticTest`, the 12-case pointer matrix unchanged, sound on the unsafe
controls, and a **canary diff with byte-identical WRONG/CRASH sets** before and after -- zero regressions.

**Where the CIL files now stop, and what byte offsets would take.** They are past the frontend and now
fail in `ReferenceElimination` on *"bare use of split variable"*: `(unsigned long)__cil_tmp9 + 8` --
integer arithmetic on the carried pointer. The blocker is a **units mismatch**, confirmed empirically:
the model addresses by **element/field index, not bytes**. `&s.c` (third field) yields offset `2`, not
`8`; `arr[i].c` is `(deref arr i)[2]`. So CIL's `+ 8` (a struct field's *byte* offset) cannot be composed
with an element offset. Making it work means carrying the offset in **bytes** and converting at every
dereference -- array index × `sizeof(elem)`, struct field → its byte offset (needing a per-struct layout
table with padding/alignment), then resolving back to the `__arrays_T[base][index]` form. That is a
change to offset semantics across the frontend, the passes and the memory model, not a local fix.

## Batch 27 — rebased onto `origin/cir-frontend`; pointer `+`/`-` now modeled

The branch was rebased onto `origin/cir-frontend` (which brings address-of-interim values and cir2c).
**Version bumped 7.2.5 → 7.3.0** — the built jar is now `theta-xcfa-cli-7.3.0-all.jar`; a stale `7.2.5`
jar lingers in `build/libs` and silently runs pre-rebase code, so always reference the 7.3.0 one.

**Rebase reconciliation (committed `fb6c957bd`).** The rebase left the data-race code split across two
APIs: the branch's atomic-aware `XcfaDataRaceCheck` (new `getDataRaceDetector`/`getDataRaceCondition`)
against cir-frontend's witness-format-2.2 writers (old `findDataRace`/`DataRace`/`DataRaceAccess`/
`wrapExprTraceCheckerWithDataRaceCondition`) — it did not compile. Resolved (user chose "keep both") by
re-exposing the old surface as **adapters over the branch's detection**, threading `parseContext` so the
witness writers stay atomic-aware. Verified: dekker → race found, GraphML witness populated with
thread_ids. **Still failing, pre-existing, NOT from this work:** `PassTests[13]` — cir-frontend tightened
`pthread_create` to require a real procedure as the thread entry, but the branch's fixture passes `thr1`
as an `Int` var. Left for the pthread owner.

**Pointer arithmetic (`p = q ± i`) — implemented, committed `92b84d25c` + `52fa58520`.** The base/offset
split (`v_base`/`v_offset`) already existed in `ReferenceElimination` for `ref(deref(B,O))`; two fixes
made it usable:
1. `*p = 5` through a split `p` wrote to **both** `p_base[0]` and `deref(p_offset,0)` (a bogus `3[0]=5`);
   now channel-splits only when the stored *value* is a pointer, so it is one cell `deref(p_base,p_offset)`.
   This alone fixed `&a[3]` (was a spurious `Unsafe`).
2. `FrontendXcfaBuilder` now lowers `p = q ± i` to `&q[i]` = `ref(deref(q,i))` (robust to CIL's bitvector
   `extract` wrapping: the pointer is the one pointer-typed leaf, the offset is the whole expr with that
   leaf zeroed, cast **signed** so subtraction and chained offsets compose), and `changeComplexAssign`
   composes when the base is itself split (`p_base=q_base; p_offset=q_offset+i`).

Validated: a 12-case matrix (correct aliasing, sound violations) + `PointerArithmeticTest` + a **canary
baseline diff** — all 13 crash/wrong canaries are identical with and without this work (the crashes are
pre-existing: `Could not determine subproperty`, `splitIf`; `AdditionIntMax` is the overflow class).
**Zero regressions.**

**CIL caveat.** The ldv driver files get *past* "Pointer arithmetic not supported" but then hit the
`container_of` / flat-addressing idiom — `(unsigned long)ptr + fieldoffset` then cast back and deref —
which **flattens a pointer to an integer**, unrepresentable in the object-id model. That is pointer↔integer
casting, a separate architectural problem, not pointer add/sub.

## Batch 26 — three grammar blockers cleared (highest-count parse-exception classes)

Picked from the 2026-07-14 run's exception scan (excluding the out-of-scope `Referencing non-variable
expressions`, 2614). Each is a HANDLE-WITH-CARE grammar change: one construct per commit, a parse-tree
**shape** test in `CTypeNameAmbiguityTest` (now 29, was 26), and a **byte-identical XCFA** sweep over all
143 canaries (110 IDENTICAL / 33 BOTH_NO_XCFA, zero NEWLY_BROKEN/DIFF_UNEXPECTED — the recurring
"NEWLY_BUILDS" flakes re-checked IDENTICAL serially). `:theta-c-frontend:test` + `:theta-c2xcfa:test` green.

1. **`parse a function-pointer cast with more than one star`** (`ecb1f6dd2`) — `(int (**)(args))`, the
   CIL idiom `*((int (**)(args))p) = &f`. `typeSpecifierFunctionPointer` accepted a single `*`; now it
   takes `pointer` (any number of stars) and `visitTypeSpecifierFunctionPointer` increments the pointer
   level once per star. ~1400 tasks had this as their first parse error.
2. **`accept an attribute inside a parenthesized declarator`** (`a505e0597`) — `void ( __attribute__((…))
   f)(args)`; `directDeclaratorBraces` now allows leading `gccAttributeSpecifier*` (ignored, as
   everywhere). ~360 tasks. Same ldv driver files as #1 hit this *first*, so the two together clear two
   layers of that stack.
3. **`parse __float128 and the __alignof that measures it`** (`620840979`) — GCC's 128-bit float, which
   appears only as the unused `max_align_t` padding `__float128 f __attribute__((__aligned__(__alignof(
   __float128))))`. `__float128` added to `typeSpecifierSimple` + `TYPE_STARTERS`, mapped to **`double`**
   (not `long double`: `CLongDouble` is unimplemented under integer arithmetic and `double` is the
   fully-supported path; precision is never observed on an unused field), and `BitwiseChecker` flags it
   FLOAT so a program that *did* compute with it stays on the float path. `__alignof` (the suffixless
   spelling) added to the sizeof/alignof operator. ~192 tasks; `ldv-regression/test_malloc-1.i` fully
   unlocks.

**Honest yield.** These remove the parse-exception *class* for the three constructs. Files whose only
blocker was one of them fully clear. But the heavily-preprocessed **ldv-linux CIL** files stack blockers:
a 12-file sample using `(int (**)…)` now parses past #1/#2 and lands on the *next* frontier —
**`UnsupportedFrontendElementException: Pointer arithmetic not supported`** (FrontendXcfaBuilder) and
`Cannot create expression of initializer list`. Those are pre-existing transformation limits, not
introduced here. So the immediate fully-solved gain is modest for the CIL family; the real measure is the
next full run, and **"Pointer arithmetic not supported"** is now the dominant downstream blocker to target.

## RESOLVED — the "alloca" false alarms were not about alloca (superseded by batch 24)

The five `termination-memory-alloca` false-`valid-deref` results reduce to a **general pointer bug,
independent of alloca**. Minimal reproductions (`scratchpad/probe/`), all deterministic in the
`--backend NONE` XCFA:

| program | verdict | note |
|---|---|---|
| `int *p=alloca(4); *p=5; assert(*p==5)` | Safe ✓ | pointee not looped |
| three allocas, no loop | Safe ✓ | multiple allocas fine |
| pointee **read** in a loop | Safe ✓ | |
| pointee written **outside** a loop (`(*i)++;(*i)++`) | Safe ✓ | |
| **pointee written *inside* a loop** (`for(*i=0;*i<10;(*i)++)`) | **Unsafe(valid-deref)** ✗ | the bug |
| same, with `&local` instead of alloca | **Unsafe** ✗ | not alloca-specific |
| same, with the pointer `i` also read after the loop | **Unsafe** ✗ | not an unused-var drop |

The symptom is exact: a pointer `i` (`= &store`, or an `alloca` result) whose pointee is written in a
loop has its `*i` **dereference base collapse to literal `0`** — the XCFA shows `0[0]` where it should
show the pointer's value (the address-taken `store` itself still correctly reads as `5[0]` on the
same edge). Base 0 is the null/unallocated class, so the deref check fires: a **false** valid-deref
violation on a safe program.

Ruled out: not alloca (repro with `&local`); not `UnusedVarPass` dropping an unused pointer (the bug
persists when `i` is read after the loop). The base is wrongly **constant-folded to 0 specifically in
the loop + pointee-write case** — leading suspect is `SimplifyExprsPass` constant propagation across
the loop back-edge, or the self-loop construction substituting the `Dereference` base. **Not yet
fixed**: the fix touches pointer/deref value-analysis where a wrong change risks unsoundness, so it
wants a focused pass-level investigation rather than a guess. This is a real missed-alarm-direction
concern only in that it *invents* violations (false positives), never hides them.

## NEXT UP (queue as of batch 25)

**~~DEFERRED (user decision, batch 25): the `psyco_math_1` soundness regression stays open.~~ FIXED
in batch 31.** It was neither a `mustNotRunUnconditionally` predicate tweak nor a `35dde5041`/
`89020cef2` revert (both stay) — the bug was in `bvOverflowCondition`, which could not read the
overflow operands through the short-circuit `Ite(cond, arith, 0)` wrapper. Added an `IteExpr` case
that recurses into `then` and guards with `cond`. `psyco_math_1` now `OK` (Unsafe); pinned by
`OverflowShortCircuitTest`. Full write-up in **batch 31** above.

## NEXT UP (queue as of batch 23)

0. ~~**unreach-call analysis-time regression (−950)**~~ — **DONE** (batches 22 + 23): the doubled
   range assume and the short-circuit guard on pure operands. All six sampled regressors now solve
   *faster than the batch-8 baseline*. The next full run should confirm the −950 is recovered.
0b. ~~**the pointer-in-loop false `valid-deref`**~~ — **DONE** (batch 24): `for (*p = 0; ...)` parsed
   as an implicit-int declaration. All five false alarms gone, one now correct.
0c. **[NEW] `Incomplete dereferences (missing uniquenessIdx)`** — exposed by batch 24: the same loop
   over an *address-taken local* (rather than `alloca`) now reaches the analysis and crashes there.
   An error, not a wrong answer, but it is the immediate next step in this area.

*(stale, kept for the record:)*
0c. hardness/eca correct →
   timeout, all profiles. Isolate by neutralising `withinTypeRange` (and separately the `Pos` bvcast
   wrap) and re-timing the fast regressors; fix the confirmed double-emission of the range assume
   either way. This is the single largest movement against us and it is a *capability* loss, not a
   soundness one — but it dwarfs every error class below.
1. **[NEW] termination-memory-alloca false-alarm cluster (5 wrong).** The alloca model reports a
   `valid-deref`/`no-overflow` violation on safe programs — a false alarm introduced since the
   baseline. Worth more than the error classes; investigate before the timeout mass.

1. **The wrong results still open** (batch 18 cleared 11 of 21): **`aws-c-common` ×3** and **`memsafety/lockfree-3.0`** (false alarms, uninvestigated), **`memory-model/{2SB,4SB}`** (missed bugs), and the two Juliet `CWE121_..._66_good` false alarms. Wrong answers are worth more than any error class.
2. **`realloc` is not modelled** and *crashes* the analysis (`IllegalArgumentException`) — found while checking free.
3. ~~**Narrow the function-pointer candidate set by parameter types**~~ — **do not do this** (batch 20): the dispatch guard is exact, so extra candidates cost only state space, while narrowing risks *dropping the true target* and silently deleting the call's side effects. The Juliet `_44`/`_65` timeouts are real, but the fix is to make the no-match branch stop being a silent havoc, not to prune the set.
4. **`memcpy` with a symbolic count** — needs a loop (new locations) in `MemoryFunctionsPass`; today such a call is left to fail loudly.
5. **The remaining error classes**: multi-dimensional array init (351), union punning (265, AD7), initializer-list expressions (220), Neutral BvType (178).
5. **N5 termination + recursion → graceful unknown**, and **D7 portfolio continues after a clean unknown** — both small, both mostly convert noise into unknowns.
6. **AD7 unions, bit-exact punning** across differently-typed members (currently rejected loudly rather than answered unsoundly) — architectural, needs the flat object layout.
7. **W5** `PRED_CART-BW_BIN_ITP-Z3` false `valid-deref` cluster (needs live debugging), **N7** Newton `MemoryAssignStmt`, **N6** `pthread_detach`.
8. **Capability/performance** (the timeout mass) — deliberately last: the profiles are only meaningful once the crash noise is gone.

*(Done since this queue was last written: **N3 division overflow** and signed-shift overflow → batch 10; **AD6 typedef-name ambiguity** → batch 10; **C1 east-const** → batch 11.)*

**→ A full re-test is warranted now**, and the local suites have been re-run under the real
`--svcomp --portfolio STABLE` (batch 20) so the green numbers can be trusted this time. Expected: the
largest frontend-error classes ("Only variable-backed functions" 1,543; asm NPE 882; unions 1,722
partially; alloca 421) should shrink. Watch for: new *wrong* results from **asm output havocing** and
from the **function-pointer no-match branch** (`havoc ret` silently skips a call whose target was not
in the candidate set — the one place the fptr model can lose a bug); and confirm the three weaver
data-race tasks moved from **wrong** to **unknown** — they no longer invent a race, but they time out
rather than prove safety, which is not a win. *(Not* fptr candidate-set breadth or union offset-0
aliasing — batch 20 probed both and neither is unsound.)

## Development directive — 2026-07-22 (libvsync → _Atomic → TDX flat memory)

New priority order set by the user. **The older execution plan below (§3, phases 1–6) is NOT
discarded — it is postponed behind this directive; the still-relevant items (TDX/union byte layout,
overflow, grammar B1–B6, function pointers, portfolio STM) remain queued and pick up after these.**

### Priority A — libvsync (104 tasks, currently 0 correct / 0 wrong / **100% ERROR**, flat across
batches 43→60). Goal: **every libvsync task parses and starts to verify (timeouts are fine).**

Blockers measured on batch60 (`error_col`):
- **66** `No such variable or macro: __atomic_compare_exchange_n` — plus `__atomic_fetch_{or,and,xor}`
  and `__atomic_thread_fence` / `atomic_fence{,_rlx,_rel,_acq}` are unmodeled. (Load/store/exchange/
  fetch_add/sub *are* handled, but **inline in `ExpressionVisitor` and NOT wrapped in an atomic
  block** — `atomicReadModifyWrite` emits two `CAssignment`s and relies on LBE to keep them on one
  edge; fragile for a concurrency library.)
- **26** `Field [tail]/[next]/[_v] not found, available fields are [...]` — struct field resolution
  picks the wrong struct type (anonymous/nested member confusion).
- **10** `Unsupported library parameter: non-zero dereference offsets are not supported`.
- **2** `Referencing non-lvalue expressions` (the `&`-of-sliced-member issue, shared with TDX).

**PROGRESS (2026-07-23).** Three of the four libvsync blockers are fixed and committed; all 19
libvsync source files now **parse** (`ParsingResult Success`):
- `f080e89f1` — **A1 atomics pass** (`AtomicFunctionsPass`): every `__atomic_*`/`atomic_*` builtin
  now lowers to an atomic-block-wrapped memory op. Validated end-to-end (concurrent fetch_add+CAS →
  Safe for unreach-call *and* no-data-race; single-threaded all-ops → Safe).
- `6aea7b717` — **nested designated initializers** (`{ .lock = { ._v = 0 } }` resolved `._v` against
  the outer struct) and **`&arr[i]` on an array of structs** (the `rowOf` region address is not a
  bare lvalue; `&` of an aggregate is the identity re-typed to a pointer). These cleared the
  `Field [X] not found` (26) and `Referencing non-lvalue` (7) errors.
- **Array-of-thread/mutex handles — FIXED (2026-07-23, commit `give each pthread array-element handle
  its own thread…`).** `pthread_create(&t[i], …)` / `pthread_join(t[i], …)` over `pthread_t t[N]` keyed
  a thread on its handle *VarDecl*, but an array element is a base/offset dereference. New
  `PthreadArrayHandleUnrollPass` (before `CLibraryFunctionsPass`, so before `ReferenceElimination`
  rewrites the handle) runs `LoopUnrollPass` — but *only* on a procedure that creates/joins through an
  array element, so nothing else is unrolled early. `LoopUnrollPass` gained an opt-in mode that folds
  each iteration's loop-variable value into the copied body (only the loop var, leaving `&x` of other
  vars for `ReferenceElimination`), turning `&t[i]` into `&t[0]`, `&t[1]`, …; `getParam` maps each
  constant `(base, offset)` to a distinct synthetic handle shared by a create and its join. `simplify`
  now recurses into `SequenceLabel` and folds `InvokeLabel` args. Verified: a 2-thread array-handle
  program races (Unsafe), mutexed form does not; canary parse + full guard set identical to baseline.
- **Now 17/19 libvsync build** (from 0). The two that still fail the frontend: `hclhlock`
  (`ReferenceElimination: bare use of split variable`) and `hmcslock` (`CInitializerList: Cannot create
  expression of initializer list`) — separate frontend gaps.
- **`WitnessOptimizer` deadlock — FIXED (2026-07-23, commit `run WitnessOptimizer only when a witness
  was applied`).** `WitnessOptimizer` is misnamed: it is not the input-witness pass (that is
  `ApplyWitnessPass`). The OC checker runs it once per thread (`oc/Utils.kt`) to normalize the segment
  counters `ApplyWitnessPass` inserts *during witness validation*; without a witness there are none and
  its only other effect (propagating thread-start literals) is redundant — `XcfaToEventGraph` already
  binds each start param. Its forward propagation deadlocked on any thread-body loop
  (`firstNotNullOf { valuations.size >= loc.incomingEdges.size }` never fires at a loop head). Gated to
  run only when the procedure references the segment-counter variable (i.e. a witness was applied).
- **Next OC blocker — `Feature not supported by OC checker: references` (`XcfaToEventGraph.exit:583`).**
  Past `WitnessOptimizer`, the OC engine (STABLE's concurrency decision procedure) rejects `&x`/pointer
  references, which the locks use throughout. This is a genuine OC-model limitation, not a crash to
  route around; the portfolio does not fall back to CEGAR here (dies with code 202). So libvsync now
  **builds** (17/19) and **starts** the OC engine, which then refuses references — the next libvsync
  step is either OC reference support or a portfolio fallback to the explicit/CEGAR engine (which does
  model references via the base/offset memory).

**A1 — all atomic operations as an XCFA pass (do first).** Route every `__atomic_*` / C11 `atomic_*`
/ `atomic_fence*` / `__atomic_thread_fence` name in the frontend to emit a `CCall` (→ `InvokeLabel`,
`params[0]`=ret, `params[1..]`=args) instead of the current inline lowering, and add a new
`AtomicFunctionsPass` in the first pass group (next to `CLibraryFunctionsPass`, before
`UnresolvedInvokeToHavocPass`) that replaces each such `InvokeLabel` with
`[AtomicBeginLabel, <stmts>, AtomicEndLabel]` (a genuine atomic block — see `AtomicBeginLabel`/
`AtomicEndLabel` in `XcfaLabel.kt`), or a `FenceLabel` for the fences. Operations: `load_n/load`,
`store_n/store/init`, `exchange_n`, `compare_exchange_n/compare_exchange` (atomic CAS: if `*p==*exp`
then `*p=des`, ret 1, else `*exp=*p`, ret 0), `fetch_{add,sub,or,and,xor,nand}`, `thread_fence`,
`signal_fence`. Memory order args are ignored (analysis is SC). Pointee type comes from the arg
pointer's `cType`. **A2 — then debug the rest** (field resolution, non-zero-offset library param,
`&`-slice) until all 104 parse+start.

### Priority B — `_Atomic` qualifier in all positions (correctness for multithreaded programs)
- **B1 — new canaries.** The sv-benchmarks MR
  (https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks/-/tree/atomic-qualifier-tasks) is checked
  out in `../sv-benchmarks` (branch `atomic-qualifier-tasks`): `c/pthread-atomic-qualifier/` — **44
  tasks** (33 `no-data-race` true, 8 `no-data-race` false, 3 `unreach-call` true). Add all as
  canaries, **keyed on the correct property per task** (they are fast to verify). Cover `_Atomic` in
  casts, arrays (incl. 2-D), pointer targets vs pointer-to-atomic, struct members, bool/char.
- **B2 — atomic alignment.** `ObjectLayout.alignBits` caps scalar alignment at the arch width
  (`Math.min(size, cap)` — the i386 `long long`→4 quirk). A power-of-2-sized `_Atomic` object must
  align to its **size**, bypassing that cap (Oracle E60778, https://docs.oracle.com/cd/E60778_01/html/E60745/gqfbq.html:
  atomic access needs natural alignment for sizes 1/2/4/8/16). Add the atomic-aware rule there.
  **TDD it** with our own `sizeof`/`alignof` unit tests against gcc-computed expectations (never by
  hand — see [[project-svcomp27-ad7-object-layout]]).

### Priority C — local benchmark. After A+B, run **locally only** on libvsync + the 44 atomic-qual
tasks; confirm parse/start (timeouts acceptable) and zero new wrong verdicts.

### Priority D — TDX module: a configurable **flat** memory model (836 tasks, 100% ERROR on the
byte-addressed-union barrier: nested aggregates + `&`-of-sliced-member). Add an *option* (keep the
current 2-D `arrays[base][offset]` as default; **both must stay usable via config**):
- **Flat layout:** every object's base is `0`; memory is byte-addressed **`Bv8`** cells. A read of a
  wider value is a `Concat` of its bytes; a narrower read is an `Extract`; a store writes the bytes.
  Saving a cell becomes trivial (no per-object base).
- **Allocation:** the current malloc grows the *base* by 3 — the flat model instead grows the shared
  *offset* by the allocation size (a bump allocator over one address space).
- **No dynamic allocation ⇒ known total size:** model memory as a **fixed-size bitvector** then.
- This is the sound way to model TDX's overlapping byte/word/register views and clears the `&`-slice
  barrier (a byte cell is a real lvalue). Sequence after Priority C.

## Batch 61 — pointer arithmetic loses its pointer type: `*(p + i)` read the wrong cell (2026-07-22)

Root-caused and fixed the false `valid-deref` on the whole Juliet CWE476 `*(dataArray + k)` family
(4 wrong results → correct `Safe`). Two independent, pre-existing bugs compounded:

1. **`p + i` was typed as an integer, not a pointer.** `visitAdditiveExpression` handed the sum to
   `getSmallestCommonType`, and `CPointer` inherits `CInteger`'s rank logic with an unset rank — so
   `pointer + int` returned an *integer* common type and wrapped the result in `mod 2^32`. That both
   truncated a 64-bit base and buried the `AddExpr` under a modulo, so the `*(p + i)` fold in
   `visitUnaryExpression` (which only peels `Pos`) no longer recognized it: `*(p + i)` became
   `deref(p + i, 0)` — reading an unallocated base — instead of `deref(p, i)`. `p[i]` (subscript)
   was unaffected because it never goes through the additive visitor. Fix: a `pointerArithmetic`
   helper in `ExpressionVisitor` emits a bare **pointer-typed** `Add(base, index)` (index scaled by
   the pointee's cell count only for aggregate pointees, no width modulo) — the exact shape the
   `*(p + i)` and subscript folds already expect, so `*(p + i)` lowers to the same `deref(p, i)` as
   `p[i]`.

2. **The load was then re-read as pointer arithmetic.** With (1) fixed, `int *d = *(pp + 2)` produced
   the correct `d = deref(pp, 2)` — but the CAssignment path's `hasArithmetic` recursed into the
   *load's own offset*, saw the addressing arithmetic, mistook the load for `d = q + i`, and rewrote
   it via `asPointerArithReference` into `d = &pp[deref(0, 2)]` (a pointer *into* `pp` at a nonsense
   offset read out of the null object). Fix: `hasArithmetic` now treats a `Dereference` as a value
   leaf — a load is never pointer arithmetic, whatever its offset does.

**Validation.** All 4 CWE476 tasks (`int/struct/int64_t/long __66_good`) go `wrong → Safe`. Canary
suite **254 PASS / 1 TIMEOUT / 0 FAIL** (the lone timeout, `admesh`, was confirmed a *pre-existing*
local timeout: the stashed pre-change build times it out identically — the harness counts TIMEOUT as
green). `:theta-c2xcfa:test` + `:theta-c-frontend:test` green (194 + 137). Regression test:
`PointerInMemoryLoadTest` pins the lowering pre-pass.

**Boundary — the DLL trio is a separate, larger problem.** `test-0504`, `test-0504_1`,
`dll_extends_pointer` stay wrong (`Unsafe`) and are *not* fixed here: they store a **mid-object**
pointer into a cell (`y->pData = &y->data`, base = `y`, offset = the field), then compare it back
(`if (&y->data != y->pData)`). A cell in the `arrays[base][offset]` model holds one base id, so the
offset is lost and the compare spuriously differs. Clearing these needs **(base, offset) pairs stored
per cell** — a real memory-model extension, distinct from the whole-pointer (offset-0) loads batch 61
handles. Left for a dedicated effort.

## Batch 62 — Priority B: `_Atomic` is a property of the accessed *cell* (2026-07-23)

Local benchmark of the atomic-qualifier MR (`sv-benchmarks/c/pthread-atomic-qualifier/`, 44 tasks)
found **26 pass / 16 false-race / 2 frontend crash**. The 16 false-races were all one root cause:
the data-race check only knew atomicity of a pointer *variable* or an address-taken object, but
`_Atomic` on a **struct field**, **array element**, **whole struct**, **nested field** or **pointee**
lives on the accessed *cell*, and by analysis time that cell is a bare `(deref base offset)` of
literals — the C type folded away (`XcfaDataRaceCheck.addressesAtomicData` only had the pointer-var
and folded-literal-pointer branches).

**Fix — record atomicity against the object's base id, which survives by value.** `ParseContext`
gained an atomic-cell map (fully-atomic objects, per-unit-offset atomic cells, and parent-cell →
subobject-base links for nesting). It is populated where base ids are minted:
`FrontendXcfaBuilder.initializeGlobalVariable`/`giveStructObjectStorage` for globals and their
struct-field subobjects, and `ReferenceElimination.globalReferredVars` for address-taken objects
(which re-base the object to the invented pointer's id — so `&s`'s struct-field access lands on that
new base, not the frontend one). `addressesAtomicData` now resolves the deref's base (a literal, or a
nested `(deref parent off)` chain via `subObjectBaseAt`) and asks the map. Also fixed
`pointsToAtomic` to consult the referred global's own `atomic` flag (the referred ref's recorded
C type had lost the atomic level for address-taken scalars — why `_Atomic int *p = &v; *p` still raced).

**Result: 40/44** (was 26), then 41/44 once the two frontend fixes below land. All object-declared-
atomic cases correct; the 8 real-race controls stay
`Unsafe` (no race hidden — verified). Alignment (B2) landed separately: `ObjectLayout.alignBits`
bypasses the i386 cap for `_Atomic` scalars (commit `align _Atomic scalars…`, `AtomicAlignmentTest`).
Regression guards: `XcfaDataRaceTest.testAtomicCellDataRace` (3 in-repo programs, no sv-benchmarks
checkout needed) and `benchmark-results/canaries/atomic_qual.tsv` (all 44, full mode). Canary parse
suite 255 PASS + 22 fixtures; guard_set full mode identical to baseline (6 pre-existing fails, none
atomic-related — confirmed by stashed-build comparison).

**Two of the four opens were then fixed (2026-07-23), → 41/44:**
- `funcptr` — commit `register a type-qualified function-pointer declarator…`. `void (* _Atomic
  fp)(void)` parenthesizes the star into the declarator, so its qualifier reached `visitDeclarator`
  (not the type specifier), where a `checkState` threw and was swallowed by the two-pass parse,
  silently dropping the whole declaration — any qualifier (const/volatile/restrict/`_Atomic`) did it.
  Now const/volatile/restrict are ignored and `_Atomic` marks the pointer variable atomic (carried on
  `CDeclaration`, applied to the function-pointer `CPointer` in `getActualType`). → `funcptr` Safe.
- `cast-ptr`'s **parse crash** — commit `require braces on a compound literal…`. The compound-literal
  rule `( type ) initializer` allowed a *bare* `assignmentExpression`, so on an assignment LHS
  `*(T*)p = v` it swallowed `p = v` as the initializer, parsed the `*` operand to null and NPE'd
  (pre-existing, not `_Atomic`-specific — `*(int*)q = 1` reproduces). A compound literal is braced, so
  the rule now requires `bracedPrimaryExpression`; the unbraced form reads as the cast it is.

**3 still open — all one mechanism (cast-through atomicity):** `cast-ptr`, `param-array`,
`param-ptr-to-atomic` all get their atomicity from a **cast** `(_Atomic int *)` on a *plain* object,
so after inline+fold the deref base is the plain object's id with no trace of the cast. This is
access-path atomicity (the pointer's pointee type at the access), which the folding/inlining model
discards — distinct from object-declared atomicity. Marking the object atomic would pass all three
but is **unsound** (it hides a real race if the same object is ever also accessed plainly), so it is
deliberately left rather than shipped as a heuristic. A sound fix needs per-access atomicity carried
through folding, or a whole-object "every access is atomic" analysis.

## Batch 63 — PLAN (no code yet): FLAT memory-model benchmark triage — run 62 (flat) vs run 61 (multi) (2026-07-24)

Two full runs finished on sosy 2026-07-24, **same build** (at/after `09daaeaf5`: flat memory model +
byte-union bitfield reads + `_Atomic`-cell atomicity), differing **only in the memory model**:
`Theta-svcomp-61` = MULTI (default; the non-disruptiveness check) and **`Theta-svcomp-62` = FLAT**
(flat as a temporary default, uncommitted). Both real & complete (0 `Cannot start process`, 55 XMLs,
tmux gone). This entry compares **flat (62) vs multi (61)** — that isolates the memory model, which is
the point of the run. Tooling: `benchmark-results/compare_runs.py <baseDir> <newDir>` (score
reproduces benchexec exactly: multi 16,320, flat 15,364). XMLs downloaded to
`results-2026-07-24_04-26-batch61/` (multi) and `results-2026-07-24_11-00-batch62/` (flat); flat
logfiles stay on sosy at `results/Theta-svcomp-62/theta27-short.xml/2026-07-24_11:00:39/…logfiles`.

| Category | multi (61) | flat (62) | Δ |
|---|---|---|---|
| correct | 10,424 | 10,693 | **+269** |
| wrong | 41 | 132 | **+91** |
| — incorrect **false** | 18 | 107 | **+89** |
| error | 25,769 | 25,412 | −357 |
| unknown | 368 | 365 | −3 |
| **score** | **16,320** | **15,364** | **−956** |

**Verdict: flat delivers its design goal but is NOT shippable as default yet.** Wins: `error→correct`
**399** (flat parses/solves pointer-heavy tasks multi couldn't) and **5 `wrong→correct`** — including
the flagship targets flat was built for: `09-regions_28-list2alloc` + `09-regions_03-list2_rc`
(no-data-race, the base/offset-loss race flat was designed to catch → now correct `false`),
`race-3_2-container_of-global`, `add_last-alloca-1` + `test22-2` (no-overflow). But flat introduces
**103 new wrong results** (`error→wrong` 97, `correct→wrong` 6), dominated by a memsafety
false-alarm flood, and the −956 score says the flood outweighs the gains. ⚠️ This **refutes** the
earlier session hypothesis that "flat memsafety is likely fine as-is (STRIDE ≡ 1 mod 3 preserves the
malloc/alloca partition)" — it is not fine on the alloca/malloc string family.

New-wrong breakdown (103): **valid-memsafety 81** (79 `false(valid-deref)` + 2 `false(valid-free)`),
no-data-race 10, no-overflow 6, unreach-call 6. Prior (multi) state of these 103: 50 were TIMEOUT,
47 frontend-failed, **6 were CORRECT in multi** (the strict regressions — see F2/F3).

### Investigation queue — flat-specific, by impact

**F1 (THE blocker — 81 tasks, −~1,300 score). valid-memsafety `false(valid-deref)`/`false(valid-free)`
flood on the alloca/malloc string family.** Every `cstr*`, `openbsd_c*`, `str{cpy,len,cmp,chr,spn,
cspn,pbrk,ncpy}*`, `mem{chr,rchr,set}*`, `strreplace/subseq/substring`, `mcslock`/`ticketlock`, and
`memleaks_test2x` variant with an `alloca`/`malloc` buffer now reports a spurious deref/free; almost
all were TIMEOUT or frontend-fail in multi, so flat both *runs* them and gets them *wrong*. Hypothesis:
flat addressing (`base = id*STRIDE`, `STRIDE = 2^16`, access folded to `deref(0, base+offset)`) breaks
the memsafety bounds check for dynamically-sized/`alloca` buffers — either the buffer's flat extent is
mis-bounded, or `base+offset` for a walked string index crosses into the neighbouring object's flat
range and trips a bounds guard that `MemsafetyPass` (which runs *before* the fold, on `base=id*STRIDE`)
set on the un-folded base. First step: reproduce `cstrcpy_malloc` and `cstrlen-alloca-1` locally under
`--memory-model flat --backend BOUNDED`, dump the emitted deref bounds vs the flat address arithmetic,
and confirm whether the violation is an off-by-object-boundary (STRIDE collision) or a mis-sized
alloca/malloc extent. This single cluster gates flat-as-default.

**F2 (UNSOUND regression — 4 tasks). no-data-race `correct→wrong/'true'`: flat now MISSES a race multi
caught.** `04-mutex_11-ptr_rc`, `05-lval_ls_05-glob_idx_rc`, `05-lval_ls_07-glob_fld_rc`,
`05-lval_ls_08-glob_fld_2_rc` (all goblint-regression, expected `false`). Multi reported the race
correctly; flat says `true`. The folding to a single flat address plausibly **merges two distinct
racing accesses** (global index / global field) into aliases that the race check then sees as the same
location, or conversely loses the distinctness needed to flag the pair. Directly opposes flat's win on
`09-regions_*` — same benchmark family, opposite direction — so worth a joint look. First step: diff
the event graph / race pairs for `05-lval_ls_07-glob_fld_rc` between multi and flat.

**F3 (regression + spurious — 6 tasks). no-overflow `false(no-overflow)`.** 2 were CORRECT in multi
(`openbsd_cstrncmp-alloca-1`, `test22-1`), 4 were frontend-fail (`cstr{cspn,len,spn}_reverse_alloca`,
`openbsd_cstrstr-alloca-1`). Same alloca-string family as F1 but on the overflow property — likely the
same flat-addressing root cause surfacing as a spurious overflow instead of a deref. First step: check
whether fixing F1 also clears these (shared alloca extent computation).

**F4 (mixed — 6 tasks). unreach-call.** 3 spurious `false(unreach-call)` (`aws_linked_list_{init,
node_reset,remove}_harness` — all frontend-fail in multi) and 3 missed-bug `true` where expected
`false` (`race-2_2-container_of`, two `linux-3.12-rc1` cil driver entry points). The aws_linked_list
trio is pointer-heavy (flat's target area) yet goes wrong — pair with F1. The 3 `true` misses are
unsound; check whether flat aliasing hides the reachable error.

### Wins to preserve (regression-guard candidates once flat is fixed)
`wrong→correct` (5): `09-regions_28-list2alloc`, `09-regions_03-list2_rc`, `race-3_2-container_of-global`,
`add_last-alloca-1`, `test22-2`. These are exactly the base/offset-loss unsoundness flat was built to
kill — lock them into the guard set so an F1 fix can't silently undo them.

### Note on run 61 (multi) vs the last downloaded run (batch60, older build)
Multi (61) vs `results-2026-07-22_09-36-batch60` (07-22 build, pre-flat/atomic/bitfield): +86 correct,
−3 wrong (44→41), score 16,227→16,320 (+93) — a clean net win from the 07-23 frontend batch. Its 9
new wrong are latent analysis bugs the parse-unlock exposed (C11 weak-memory race misses in
`reorder_c11_good-*`, `rec_ticketlock` spurious race, `test-bitfields-2-2` bitfield deref,
`aws_string_new…negated` missed bug) — tracked separately from the flat work; not the subject of this
plan. `compare_60_61.py` retains that diff.

## Batch 64 — PLAN (immediate next step after Batch 63/TDX F1 flood fix): libvsync remaining issues — 4 wrong verdicts + 2 hard blockers (2026-07-25)

Queued as the **next thing after the Batch 63 TDX flat-model flood (F1) is fixed** — picks back up
Priority A/C from the 2026-07-22 directive, whose stated goal ("every libvsync task parses+starts;
timeouts fine; **zero new wrong verdicts**") is currently violated by 4 tasks. Source: batch62
(`results-2026-07-24_11-00-batch62`), the latest downloaded round covering libvsync (17 no-data-race +
12 unreach-call + 14 valid-memsafety = 43 run instances). Current state: 1 correct, **4 wrong**, 38
timeout/OOM/error — a big improvement over batch61 (most tasks frontend-failed there; see the A1/A2
progress notes above) but not clean.

### L1 (blocker — 2 tasks). Frontend/solver hard failures, unrelated to each other
- **`hmcslock.yml`** — still dies in the frontend: `CInitializerList: Cannot create expression of
  initializer list`. Flagged in the 2026-07-23 progress note ("two that still fail the frontend:
  hclhlock and hmcslock") and never revisited after hclhlock's blocker (bare-split-variable) was fixed
  alongside the array-handle work. Needs its own root-cause pass.
- **`hclhlock.yml` / `rwlock.yml`** — now parse (progress), but both crash post-parse with
  `com.microsoft.z3legacy.Z3Exception: theory not supported by interpolation or bad proof`
  (unreach-call + valid-memsafety, both tasks; no-data-race instead OOMs on hclhlock). This is a *new*
  blocker only exposed once parsing got past the array-handle/atomics fixes — likely a CEGAR
  interpolation config hitting a theory (array-of-struct or bitvector-in-array shape from the lock's
  node array) it can't interpolate. First step: reproduce `hclhlock` locally under the exact failing
  portfolio config with `--debug --stacktrace`, identify which domain/interpolation combo issues the
  unsupported query, and either route around it (drop that config from the libvsync-relevant portfolio
  slice) or fix the interpolation gap.

### L2 (soundness — 4 tasks). New/latent wrong verdicts on libvsync
| Task | Property | Expected | Got |
|---|---|---|---|
| `bounded_mpmc_check_full.yml` | no-data-race | true | `false(no-data-race)` |
| `rec_ticketlock.yml` | no-data-race | true | `false(no-data-race)` |
| `mcslock.yml` | valid-memsafety | true | `false(valid-deref)` |
| `ticketlock.yml` | valid-memsafety | true | `false(valid-deref)` |

`rec_ticketlock` is not new — already named as a "latent analysis bug the parse-unlock exposed"
(`rec_ticketlock` spurious race) in the batch60→61 note above; the other 3 are new since batch61
(where they frontend-failed instead, so never got a verdict). All 4 are false positives (Unsafe
reported on a Safe task) — same failure shape as **W6** (OC checker false positives, §1) and the F2
flat-race-merge regression in Batch 63 — worth checking whether they share a root cause before treating
each independently:
- `bounded_mpmc_check_full` + `rec_ticketlock` (no-data-race, spurious race): diff the OC event graph /
  race pair against a known-correct sibling (same approach as F2's "first step"); check whether the
  atomics pass's `AtomicBeginLabel`/`AtomicEndLabel` wrapping (A1, 2026-07-23) is too coarse and
  serializes/desyncs otherwise-independent accesses into a false race, or too narrow and misses that an
  op is atomic.
- `mcslock` + `ticketlock` (valid-memsafety, spurious deref): both are lock queue/ticket structures
  walked through array-element handles — check interaction with `PthreadArrayHandleUnrollPass` (the
  2026-07-23 array-handle fix): does the per-iteration constant-folded `(base,offset)` handle produce a
  bounds check that the *real* (loop-driven) access pattern would satisfy but the unrolled/folded one
  doesn't line up with memsafety's bounds tracking?

### L3 — after L1+L2: re-run Priority C
Once L1's two hard failures are resolved or explicitly routed around and L2's 4 wrong verdicts are
fixed or reclassified as pre-existing/out-of-scope, re-run Priority C as originally scoped: a full
local pass over libvsync (104 tasks) + the 44 atomic-qualifier tasks (Priority B), confirm parse/start
(timeouts fine) and **zero wrong verdicts**, then fold the libvsync + atomic-qual tasks into the canary
guard set so this doesn't silently regress again.

## 0. Result summary

| Category | Count | Notes |
|---|---|---|
| correct | 5,917 | |
| **wrong** | **13** | 5 false-negatives ("true" on unsafe task), 8 false-positives ("false" on safe task) |
| unknown | 27 | portfolio short-circuits on a clean `unknown` (see D7) |
| error: frontend failed (before parsing finished) | 14,610 | crashes in ANTLR grammar or C-transformation |
| error: frontend failed (after parsing finished) | 2,960 | crashes in XCFA passes (overflow pass dominates) |
| error: solver error | 31 | |
| error: TIMEOUT | 10,607 | ~1,300 of these are crash-induced (see N below) |
| error: OUT OF MEMORY | 2,437 | |

Analysis artifacts (parsed TSV of all runs, log-diagnostic JSONs, scripts) are in
`/tmp/claude-1000/-home-levente-Documents-University-theta/c308a768-771f-496e-ad75-ec5fece4b54e/scratchpad/analysis/`
(`runs.tsv`, `log_diags.json`, `per_task_diag.json`) — **copy these somewhere permanent before the session's tmp dir is cleaned** if you want to reuse them.

---

## 1. Wrong results — categorized (13 tasks)

### W1. Integer-literal typing ignores `U` suffix → wrong verdicts under integer arithmetic (2 tasks) — LOCAL BUG
`bitvector-regression/signextension2-1.yml` (expected true → got false), `signextension2-2.yml` (expected false → got true). **Repro'd on master.**
- `ExpressionVisitor.java:832-840` (`visitPrimaryExpressionConstant`): the `signedLongLong`/`signedLong` branches lack a `!isUnsigned` guard, so `4294967295UL` on ILP32 is typed **signed long long** instead of `unsigned long`. The comparison `castToLong != 4294967295UL` is then done in signed-64 semantics and evaluates wrongly.
- Aggravated by **W2** below (casts to wider signed types are identity).

### W2. `CastVisitor` (integer arithmetic): signed-target casts never wrap — LOCAL BUG, decision RESOLVED
`subprojects/frontends/c-frontend/.../visitors/integer/CastVisitor.java` — every signed-target cast contains `if (true) { return Pos(param); }` making the correct `Sub(Mod(Add(...)))` logic below it **dead code**. Only unsigned-source-same-width is handled (`handleUnsignedSameSize`). Any narrowing or signed→signed cast silently keeps the mathematical value.
- **Decision (resolved)**: signed integer overflow/wraparound is undefined behavior in C standards before C23, so modular semantics must not be silently assumed. Add a `FrontendConfig` option **`--enable-signed-wraparound`** that, when set, activates the modular-wraparound logic (the currently-dead `Sub(Mod(Add(...)))` path) for signed-target casts; default remains off. Plumb it through `CFrontendConfig` → `ParseContext` → the integer `CastVisitor`. The W1 literal-typing fix is independent and lands regardless.

### W3. `__VERIFIER_nondet_memory` is silently a no-op → vacuous "Safe" (1 task) — LOCAL BUG
`nondet-memory-examples/nondet_struct.yml` (expected false → got true).
- `NondetFunctionPass.kt:36-38` always havocs `params[0]`, which is the synthetic *return-value slot* prepended by `FrontendXcfaBuilder.kt:495-505`. For `__VERIFIER_nondet_memory(ptr, size)` the pointer arg at `params[1]` is never havoc'd; the call vanishes from the model entirely (verified by inspecting generated `xcfa.c`).
- Fix: special-case pointer-argument nondet intrinsics (havoc the pointee region), or at minimum bail out with "unsupported" instead of silently dropping.

### W4. Memsafety encoding: no scope/lifetime invalidation → missed violations (2 tasks) — decision RESOLVED
`memsafety-ext3/scopes1.yml` (expected false(valid-deref) → got true), `ldv-memsafety/memleaks_test3-1.yml` (expected false(valid-free) → got true), both proved "Safe" by KIND.
- `PtrSize.kt`: `deallocate()` is called **only** from `MemsafetyPass.annotateFree` (heap `free()`). Stack variables' validity entries are never invalidated at block/function exit, so dangling-pointer derefs look valid forever.
- **Decision (resolved)**: lifetime tracking is implemented in **`FrontendXcfaBuilder`** (c2xcfa), where exact lexical-scope information is still available (XCFA passes only see the flattened procedure) — emit `deallocate()` for address-taken locals at block/function scope exit, **gated on the verified property demanding it** (MEMSAFETY/valid-memcleanup; skip for plain reachability to avoid needless model bloat). Mind interactions with `ReferenceElimination` (which emits the matching `allocate`s) and gotos/early returns crossing scope boundaries (every scope-exiting edge needs the deallocation, not just the syntactic block end).

### W5. CEGAR `PRED_CART-BW_BIN_ITP-Z3` false `valid-deref` cluster (6 tasks) — UNPINNED, needs live debugging
`termination-recursive-malloc/rec_strcopy_malloc`, `memsafety-ext3/getNumbers1-2`, `memsafety-ext3/scopes4-1`, `memsafety-cve/hyperkit_1Fixed`, `busybox-1.22.0/hostid` (all expected true → got false(valid-deref)); also `termination-crafted/Stockholm-2.yml` (no-overflow, expected false → got **true/Safe** via the same config — the only wrong *Safe* from CEGAR).
- All produced by the same portfolio config; `cexMonitor=CHECK` is on, yet a concretizable-looking counterexample was reported. Static exploration could not pin the bug (candidates: Cartesian-abstraction + `Fitsall` array bound reasoning, interpolant validity, or a `MemsafetyPass` encoding edge case, e.g. string literals / `alloca` sizes).
- Plan: reproduce one task (`getNumbers1-2.c` is small and fails in ~57s) with `--backend CEGAR --domain PRED_CART --refinement BW_BIN_ITP` + `--debug --stacktrace`, dump the abstract ARG + refined trace, and check whether the reported trace is actually concretizable. This is an **investigation task, not yet a fix task**.

### W6. OC (ordering-consistency) multithreaded checker false positives — NOW IN SCOPE (2026-07-16)
The external OC PR has been merged into this branch, so OC is no longer separate — the concurrency/OC
wrong results are ours to fix. `pthread/singleton.yml` (memsafety, expected true → got
false(unreach-call), **"Unsafe, Trace length: 0"**), `goblint-regression/04-mutex_17-ps_add1_nr.yml`
(no-overflow, expected true → got false, trace length 20).
- Starting points to re-verify against the merged code (were from before the merge, confirm they still
  apply): `XcfaOcChecker.kt:131-146` swallows trace-extraction exceptions and still reports
  `SafetyResult.unsafe(EmptyCex, ...)`; forced 2-iteration loop unroll (`XcfaOcChecker.kt:60-70`) has a
  Safe-only reliability downgrade (`ExecuteConfig.kt:300-315`), never Unsafe; MULTITHREAD portfolio
  dispatches OC on memsafety/overflow-lowered `ERROR_LOCATION` properties (`MemsafetyPass.kt:82`,
  `multithread.kt:210-285`). The 2026-07-16 run has ~60 `pthread-wmm` `false(valid-deref)` false alarms
  — the dominant OC cluster to root-cause.

---

## 2. Exceptions — categorized (root causes with counts)

Frontend crashes kill the **entire run before the portfolio starts** (single up-front parse: `ExecuteConfig.kt:74-79`; `XcfaParser.kt:118-124` calls `exitProcess`), so each of these counts is a task with zero verification attempts.

### Parse errors (ANTLR grammar, `C.g4`) — 4,108 tasks
| Cause | ~Tasks | Grammar location | Difficulty |
|---|---|---|---|
| **B1** Cast to function-pointer/array-pointer abstract declarator `(int(**)(...))`, `(float(*)[4])`, `*((void(**)...)` | 2,080 | `castDeclarationSpecifierList` (C.g4:217-220) never uses `abstractDeclarator`; only hardcoded single-`*` alternative (C.g4:278) | moderate (targeted alternatives) / ⚠️ hard (proper `abstractDeclarator` unification — reintroduces `(expr)` vs `(type)` ambiguity) |
| **B2** `typedef struct/union __attribute__((...)) {...}` | 836 | `structOrUnionSpecifier` (C.g4:286-289) has no attribute slot after keyword | trivial |
| **B3** `__attribute__` before pointer in parenthesized declarator `void *(__attribute__((...)) *f)(void)` | 513 | `declarator`/`directDeclaratorBraces` (C.g4:365-371) | moderate |
| **B4** `__builtin_va_arg(x, void **)` — type name as call argument | 334 | commented-out rules at C.g4:43-44 | moderate (grammar + visitor) |
| **B5** bitfield/struct-member attributes (`struct __sFILE` cluster) | 132 | `structDeclarator` (C.g4:319-322) | trivial |
| **B6** parenless `sizeof expr` / `sizeof *p` | 85+ | `unaryExpressionSizeOrAlignOf` (C.g4:124-126) only has parenthesized form | moderate (visitor must infer type of expr) |
| **B7** typeof/statement-expr reported failures | 92 | NOT reproducible standalone — likely secondary fallout of B1/B3/B6 | re-measure after B1-B6 |
| misc (`}`, `<EOF>`, container_of chains) | ~120 | assorted | re-measure after B1-B6 |

Note: fixing B1 alone only moves ~2k tasks to the *next* error ("Function pointers not yet implemented", `TypeVisitor.java:235-238`) unless P2 (function pointers) also lands; product-lines tasks may still verify because the casts are often in dead code — pruned by `GlobalDeclUsageVisitor` — measure after fixing.

### Transformation errors (c-frontend visitors) — ~9,900 tasks
| Cause | ~Tasks | Location | Difficulty |
|---|---|---|---|
| **C1** `GlobalDeclUsageVisitor` swallows `Throwable` per top-level decl → truncated usage sets → reachable functions pruned → "No such variable or macro: printLine" etc. **Repro'd**: `char const *` param alone breaks it | ~1,500+ (all 1,454 printLine/Juliet + share of atoi/typedef misses) | `GlobalDeclUsageVisitor.java` (blanket catch), triggered by east-const (`char const *`) parameter handling | small-moderate: fix east-const in declaration processing AND stop swallowing (log + treat decl as used) |
| **C2** Enum constants never registered as values. **Repro'd**: `enum {A=1}; x=A;` fails | ~1,500 (SOCK_STREAM 1,314 + TRUE/STATE_1/pi/…) | `TypeVisitor.visitEnumDefinition` (TypeVisitor.java:293-307) drops enumerator values; `mergeCTypes` substitutes `int` | moderate: enumerator symbol table + constant folding of the init `constantExpression` |
| **C3** `__builtin_*` unsupported (alloca, isnan, isgreater*, va_start, bswap, atomic_store_n…) | ~700 | `MacroExprs.kt:23-124` hardcoded macro list; no builtin concept | moderate: map float-classify builtins to FpExprs, `__builtin_alloca`→malloc-like, rest → graceful unsupported |
| **C4** `&expr` only for plain variables ("Referencing non-variable expressions is not allowed!") — `&a[i]`, `&s.f` | 1,144 | `ExpressionVisitor.java:673-678` | **OUT OF SCOPE — being fixed in a separate PR.** Keep sample tasks in the canary/guard sets only. |
| **C5** Function pointers not modeled ("Only variable-backed functions are callable") | 1,167 | `ExpressionVisitor.java:937-942`; local fptr vars never enter `functions` map (FunctionVisitor.kt); no indirect-call pass exists | ⚠️ architectural, approach decided: fptr-typed variables + indirect-call dispatch pass using **candidate sets** (see Phase 6) |
| **C6** `namedType should be short or long...` — `_Complex`, `__m128*` etc. as non-main specifier | 920 | `NamedType.patch` (NamedType.java:148-183) | small: enumerate missing cases, degrade to warning like `getActualType` |
| **C7** inline `asm` statement → visitor returns null → NPE in `CCompound.addCStatement:47` | 790 | unlabeled asm alternative in `statement` (C.g4:488-496); `FunctionVisitor.visitStatement` | trivial: label the alternative, return no-op statement; audit other unlabeled alternatives |
| **C8** Unions dropped ("Only structs expected here") — `union{...}` becomes `int` | 658 | `TypeVisitor.visitCompoundDefinition` (TypeVisitor.java:241-274) | ⚠️ architectural, approach decided: model fixed-size arrays/structs/unions as large bitvector objects with extraction-based access (see Phase 6); no interim union-as-struct hack |
| **C9** Self-referential struct: `Struct.copyOf()` snapshots empty fields map ("Field [next] not found, available fields are: []") | 613 | `Struct.java:57-64,102-107` copy-ctor `putAll` during construction; `visitTypeSpecifierPointer` calls `copyOf()` | small: lazy/by-name field resolution in the pointer-member path |
| **C10** `sizeof(unknown-name)` NPE (`getVar(...).getRef()` unchecked) | 400 | `ExpressionVisitor.java:558-582` | trivial: null-guard + existing "unknown type, using 0" warning path |
| **C11** Initializer gaps: nested initializer lists (200), multi-dim array init (62, `FrontendXcfaBuilder.kt:150,239`), designators (36, `DeclarationVisitor.java:102`), compound casts (57, bitvector `CastVisitor.java:99,137`) | ~355 | as listed | moderate each; designators+multi-dim are contained; flag compound-cast as needs-design |
| **C12** Neutral BvType from `~x` (175) + strict `TypeUtils.cast` width mismatch on bv literals (212) | 387 | `ExpressionVisitor.java:668-672` (`BvType.of(width)` without signedness); literal-width desync feeding `TypeUtils.cast:107` | first: one-liner (pass signedness); second: needs a failing case to pin |
| **C13** Hex-int literals containing `e` (0xCAFE) and char literals `'e'`/`'.'` misrouted to float parsing | 34 | `ExpressionVisitor.java:756-787` — `text.contains("e")` before hex check | trivial |

### Pass/analysis-time errors — ~3,600 tasks (mostly counted under TIMEOUT)
| Cause | ~Tasks | Location | Difficulty |
|---|---|---|---|
| **N1** Unknown extern function calls survive to analysis: "No such method time." etc. — config crashes, portfolio burns budget → TIMEOUT | ~1,390 (time 1,320; _setjmp, calloc, memset, sin…) **Repro'd** | `XcfaAnalysis.kt:141,167`, `XcfaState.kt:126`; only `printf/scanf/pthread_*` (`CLibraryFunctionsPass.kt`), `malloc` (`MallocFunctionPass.kt` — literally only "malloc", not calloc/realloc), `__VERIFIER_nondet*` (`NondetFunctionPass.kt`) are handled | **Decision (resolved)**: final catch-all pass havocing the return value of every unresolved `InvokeLabel`, emitting a **warning that side-effects of the call may be swallowed** (out-params like `time(&t)`, `memset` are not modeled). Add `calloc`/`realloc` to the malloc pass separately with real semantics. |
| **N2** `OverflowDetectionPass` hard-aborts on whole-file bitvector mode ("does not yet support bitwise arithmetic") | 1,478 | gate at `OverflowDetectionPass.kt:84`; root cause: bitvector `LimitVisitor` is a stub returning `Assume(true)`; and arithmetic is a whole-file decision (`FunctionVisitor.java:157-166` + `BitwiseChecker`) — one `&` or a float anywhere flips the file | moderate: implement real bitvector LimitVisitor (extended-width or bv-overflow predicates), then remove gate |
| **N3** Overflow + division: unconditional throw ("cannot soundly detect overflows with divisions") | 683 | `OverflowDetectionPass.kt:236-238`; frontend wraps `/` in `Ite`-corrected floor-div so the raw `DivExpr` is an encoding artifact | well-scoped: detect the `createIntDiv` shape; overflow condition is just `dividend==MIN && divisor==-1` |
| **N4** Logger `String.format` on dynamic strings containing `%` (`UnknownFormatConversionException`) | 63 (+hidden crashes) | `BaseLogger.java:30`; misuse at `stm.kt:71,158,161`, `ExecuteConfig.kt:310`, `TraceGenLogging.kt:101`, `XcfaParser.kt:219`, `StsCli.java:495`, … | **Decision (resolved)**: fix the misusing call sites (pass `"%s"` as pattern with the dynamic string as argument); do **not** add skip-format-when-no-varargs logic to `BaseLogger`. Audit all `logger.write`/`benchmark`/`result` call sites passing interpolated strings as the pattern. |
| **N5** Termination: `error("Only single-procedure or inlineable programs...")` — every recursive termination task dies | large share of 1,996 termination errors | `termination.kt:231-233` | ⚠️ architectural: recursion support for termination, or graceful `unknown` |
| **N6** no-data-race: `DataRaceUtils.kt:203` "Unknown procedure: pthread_detach/strcpy/…" | 21 | `isLibraryFunction` covers only 3 pthread fns (`CLibraryFunctionsPass.kt:179-184`) | small, but **semantics-sensitive**: each newly supported `pthread_*` function must be modeled with its real semantics (e.g. `pthread_detach` affects joinability, not a no-op for `pthread_join`-using programs), not blanket-added to a "library/no-op" list. Non-pthread names (`strcpy`, `time`, `calloc`) fall under the N1 catch-all + warning. |
| **N7** Newton refiner: `MemoryAssignStmt not supported` | 8 | `ExprTraceNewtonChecker.java:306+`, `SpState.java:153`, `WpState.java:159,233` | **encode properly instead of skipping**: `MemoryAssignStmt` is an array write, so pre/post conditions follow McCarthy array axioms — WP: `wp(mem[i] := v, Q) = Q[mem ← store(mem, i, v)]`; SP: introduce fresh `mem'` with `mem' = store(mem, i, v)` and substitute. Implement in `WpState`/`SpState` and the Newton checker's statement visitor, mirroring the existing `ArrayWriteExpr` handling used by other refiners. |
| **N8** misc: local mutex handles (10), "Main function not found" (13), NotSolvable (11), Z3 legacy interpolation errors (16), hex-FP constants (24 — see C13/its sibling at `ExpressionVisitor.java:782`) | ~90 | as listed | assorted small |

### Capability limits (not crashes) — ~11,600 TIMEOUT/OOM
By portfolio: FLOAT 3,491 (worst ratio: 652 correct), PTR 2,952, ARR 1,370, BITWISE 875, NONLIN_INT 1,074, LIN_INT 790, TERMINATION 786, MULTITHREAD 479. Top families: `hardness` 4,689, Juliet 2,610 (mostly N1-induced), `hardware-verification-bv` 1,016, `eca-rers2012` 980.
These need algorithmic/portfolio work (out of scope for bug-fixing phases; see Phase 6).

Special note — **Huawei-Concurrency-Challenges demo: 71/71 tasks error** (asm-NPE 43, `&expr` 14, `__atomic_*` 5, unions 9). C7+C3+C8 from this plan plus the external `&expr` PR (C4) cover the entire demo category's frontend story; high visibility, worth prioritizing.

---

## 3. Execution plan

Ordering rationale: (1) SV-COMP scoring punishes wrong results (−16/−32) far more than errors (0), so soundness first; (2) then trivial fixes with huge unlock counts; (3) then grammar; (4) then the overflow property; (5) architectural features last, each behind a design note. Items within a phase are independent and can be parallelized.

### Phase 0 — Test infrastructure (prerequisite, ~1-2 days)
1. **Regression corpus**: create `subprojects/xcfa/c2xcfa/src/test/resources/` fixtures per bug class (25enum.c, 26union.c, 27selfrefstruct.c, 28asm.c, 29eastconst.c, 30hexlit.c, 31vaarg.c, 32sizeof.c, 33castfnptr.c, 34fptr.c…), added to `TestFrontendXcfaBuilder.kt::data()`. Every fix below lands with its fixture.
2. **Canary task suite** (replaces reliance on the existing `integration-tests/software/` suite, which is a smoke test rather than a full regression net): from `runs.tsv`, sample the **correctly solved** tasks of the last benchmark run **with cputime < 60s, stratified per sv-benchmarks subfolder** (1-2 per subfolder), and add them to the integration tests with their expected verdicts. These are the canaries in the coal mine for every refactor — especially the grammar and object-encoding work. Automate the sampling (script reads `runs.tsv`: `category == correct && cputime < 60`, group by task-path folder).
3. **Frontend parse-only canaries**: for frontend crash testing, run tasks with **`--backend NONE`** so only parsing/transformation executes, not the expensive analysis. Two uses: (a) the currently-crashing samples per failure category (≤15/category, from `runs.tsv` `error_col`) must stop crashing; (b) **all** canary tasks from step 2 must keep parsing after every grammar change — this is the cheap, wide net against grammar regressions.
4. **Category spot-check script**: runner that executes the built archive (`./gradlew buildArchiveTheta-svcomp` → `subprojects/xcfa/xcfa-cli/build/distributions/Theta-svcomp.zip`) on the sampled tasks with the exact benchmark flags (`--svcomp --portfolio STABLE --property … --architecture …`), and diffs the outcome class (crash class / verdict) before vs after.
5. **Wrong-result guard set**: the 13 wrong tasks + their 6 nearest correct neighbors run on every phase completion; any new wrong verdict is a hard stop. (The 2 OC tasks stay in the set to observe the external OC PR's effect, not ours.)

### Phase 1 — Soundness (wrong results) 
| Step | Fix | Effort | Test |
|---|---|---|---|
| 1.1 | W1 literal typing: add `!isUnsigned` guards (`ExpressionVisitor.java:834,837`) | trivial | signextension2-1/2 improve; unit test literals `4294967295UL`, `2147483648U` on ILP32/LP64 |
| 1.2 | W3 `NondetFunctionPass`: handle `__VERIFIER_nondet_memory` (havoc pointee or reject) | small | nondet_struct → false or unknown, never true |
| 1.3 | W2 signed-cast wraparound behind new **`--enable-signed-wraparound`** `FrontendConfig` option (default off; option enables the modular-wrap path in the integer `CastVisitor`). **Nothing sets it currently** — SV-COMP does not mandate modular signed semantics, and wraparound would break overflow detection. Add an **input-flag validation rule** rejecting `--enable-signed-wraparound` combined with the overflow property | small-moderate | unit tests for the flag's cast semantics; **CLI validation test: `--enable-signed-wraparound` + no-overflow property must be rejected**; canary suite (flag off everywhere) verdict-identical; signextension2 guard tasks expected to be fixed by 1.1 alone — verify |
| 1.4 | W5 investigation: live-debug `getNumbers1-2.c` under PRED_CART-BW_BIN_ITP; outcome = pinned bug + fix or a gating decision (e.g. disable that config for MEMSAFETY until fixed) | investigation | the 6-task cluster → true or unknown |
| 1.5 | W4 memsafety scope-lifetime (decision resolved): emit `deallocate()` at scope exit for address-taken locals in **`FrontendXcfaBuilder`**, gated on the property demanding it (MEMSAFETY/memcleanup); cover gotos/early returns crossing scopes | moderate | scopes1, memleaks_test3-1 → false or unknown; memsafety canaries stay correct; fixture with goto-out-of-block dangling pointer |

(W6 / OC items are now in scope — the OC PR was merged into this branch on 2026-07-16. The ~60
`pthread-wmm` `false(valid-deref)` false alarms in the 2026-07-16 run are the dominant OC cluster.)

### Phase 2 — Trivial/small crash fixes, large unlock (~5,000 tasks)
| Step | Fix | Unlocks | Test |
|---|---|---|---|
| 2.1 | N4 logger: fix misusing call sites to pass `"%s"` + argument (no `BaseLogger` behavior change) | 63+ hidden | unit test asserting a `%`-containing dynamic message logs verbatim through the fixed call sites |
| 2.2 | C7 asm statement: label grammar alt + no-op statement; audit unlabeled alts (grammar change — Phase 4 caution rules apply) | 790 | 28asm.c fixture; ldv sample; full canary `--backend NONE` parse sweep |
| 2.3 | C9 `Struct.copyOf` self-reference fix | 613 | 27selfrefstruct.c (`list_head`) |
| 2.4 | C10 sizeof NPE null-guard | 400 | 32sizeof.c |
| 2.5 | C13 numeric-literal classification (hex before `contains("e")`; char literals) | 34 | 30hexlit.c with `0xCAFE`, `'e'` |
| 2.6 | C1 east-const + `GlobalDeclUsageVisitor` hardening (narrow the catch; on walk failure, conservatively mark decl used) | ~1,500 | 29eastconst.c (`char const *` param); 3 Juliet tasks incl. valid-memcleanup (currently 0 correct in that whole category) |
| 2.7 | C6 `NamedType.patch` missing specifiers → warn-and-continue | 920 | fixture with `double _Complex` prototype |
| 2.8 | C2 enum constants (symbol table + constant folding) | ~1,500 | 25enum.c (named, anonymous, explicit+implicit values, enum in switch); SOCK_STREAM Juliet task |
| 2.9 | N6 pthread coverage: model `pthread_detach` (and any other newly supported `pthread_*`) with **correct semantics** — verify against pthreads spec how each interacts with join/exit/data-race detection before adding; do not blanket-list as no-ops | 21 | goblint no-data-race sample; concurrency canaries stay correct |
| 2.10 | N7 Newton refiner: implement WP/SP encoding of `MemoryAssignStmt` via array `store` (McCarthy axioms) in `WpState`/`SpState`/`ExprTraceNewtonChecker` | 8 | unit test WP/SP of `mem[i]:=v` against hand-computed formulas; NWT config on a PTR-portfolio sample |
| 2.11 | C3 builtins: `__builtin_isnan`&co → FpExprs, `__builtin_alloca` → malloc-equivalent, bswap/expect/object_size; graceful unsupported for va_start | ~700 | fixtures per builtin; float sample tasks |

### Phase 3 — Unknown-extern-function handling (decision resolved, ~1,400 tasks)
- N1: add catch-all pass converting **all unresolved `InvokeLabel`s** to a havoc of the return variable, and **print a warning stating that side-effects of the call may be swallowed** (out-params/globals written by the callee are not modeled). No pointer-reachable havocking in this phase.
- Extend `MallocFunctionPass` to `calloc`/`realloc` with real size/zeroing semantics; model `memset`/`memcpy` minimally where cheap.
- Test: `time()` repro fixture; Juliet fscanf sample (currently TIMEOUT storm); assert Juliet no-overflow sample now yields verdicts and the warning appears in the log.

### Phase 4 — Grammar (B1-B6, ~4,100 tasks) — ⚠️ HANDLE WITH CARE
**Grammar modifications can introduce subtle bugs** (new ambiguities silently changing how *previously-working* programs parse, not just failing loudly). Mandatory guardrails for every `C.g4` change, however small:
- One construct per commit; never batch grammar changes.
- After each change, run the **full canary suite with `--backend NONE`** (Phase 0.3) and diff: (a) zero new parse failures, and (b) for a sampled subset, the emitted XCFA (`--output`) is byte-identical for programs not exercising the new construct — catches silent reinterpretation, not just rejection.
- Regenerate with the build's `-Werror` (warnings fail the build) and additionally run ANTLR's diagnostic/ambiguity listener over the canary corpus in a test to surface new ambiguity reports.
- Grammar fixture tests must include *negative* neighbors (constructs that must keep failing or keep their old parse tree).

Order: B2+B5 (attribute slots — needed by Phase 6 packed/aligned work too) → B3 (declarator attributes) → B6 (parenless sizeof) → B4 (`__builtin_va_arg`) → B1 (casts).
- **B1 decision (AD6 resolved): `abstractDeclarator` unification**, with the `(expr)` vs `(type)` ambiguity resolved **context-sensitively**: at parse time the set of type names is fully known (built-in specifiers + typedef names encountered so far in the already-preprocessed translation unit), so `(` X … `)` is a cast iff X starts a type. Implementation: maintain a typedef-name symbol table during parsing (fed by `declaration` visits/listener — the classic "typedef feedback" approach) and gate the cast alternative with an ANTLR semantic predicate consulting it; scoping matters (a local variable can shadow a typedef name — track scope depth). `castDeclarationSpecifierList`/`typeSpecifierFunctionPointer` (C.g4:217-284) are then retired in favor of `typeName` + `abstractDeclarator` (C.g4:435-456), which also naturally fixes B6's `sizeof(typeName)` vs `sizeof(expr)` disambiguation.
- **Dedicated ambiguity test suite in the parsing submodule** (`subprojects/frontends/c-frontend` — new test source set, testing the parser directly without the downstream pipeline): be **as creative as possible in confusing `(expr)` vs `(type)`**, e.g.: `(a)(b)` with `a` as typedef vs as function; `(a)*b` (cast-of-deref vs multiplication); `(a)-b`, `(a)+b`, `(a)&b`; `sizeof(a)` both ways; `(a)(*b)(c)`; typedef name shadowed by a local variable and then used in both roles in sibling scopes; `(unsigned)(a)`; `(a*)(b)`; nested `((a)(b))(c)`; comma expressions `(a, b)`; compound literals `(struct s){0}` if supported. Every case asserts the resulting parse tree shape (cast vs call/mul/etc.), not just parse success.
- After B1-B6 land, re-run the parse-category spot-check and re-measure B7/misc (expected to shrink).
- Test: fixtures compile through `getXcfaFromC`; product-lines + intel-tdx + aws-c-common + neural-networks samples (3 each); full canary parse sweep after every commit.

### Phase 5 — Overflow property (N2+N3, ~2,160 tasks; no-overflow currently 1,200 correct / 7,838 error)
1. N3 division: special-case `INT_MIN/-1` condition (`OverflowDetectionPass.kt`), recognizing the `createIntDiv` Ite shape. Well-scoped.
2. N2 bitwise: implement real bitvector `LimitVisitor` (bv overflow predicates or extended-width comparison), remove the `check()` gate at `OverflowDetectionPass.kt:84`. Add signed-shift overflow semantics while there (currently silently unchecked in both modes).
3. Add `OverflowDetectionPass` entries to `PassTests.kt` (currently zero coverage).
- ⚠️ Note the whole-file arithmetic flip (one `&` → BITVEC → gate) also interacts with `--enable-signed-wraparound` (Phase 1.3) and the objects-as-bitvectors encoding (Phase 6.1, which force-enables bitvector mode) — coordinate all three.
- Test: mlceu.c, bAnd1.c, standard_palindrome samples; Juliet no-overflow batch of 15; verify verdicts against expected, not just non-crash (overflow encoding bugs produce wrong results, not errors).

### Phase 6 — Architectural features
(`&expr` addressable-lvalue support is **not here** — separate PR.)

1. **C8 + object encoding restructuring — objects as bitvectors** (unions 658 tasks + foundation for structs/arrays; decision resolved). Model **fixed-size arrays, structs, and unions as large bitvector objects**, where every member/element access is a bit **extraction** (reads) / insertion (writes) at the member's computed bit offset:
   - **Layout computation** must honor `__attribute__((packed))` and `__attribute__((aligned(n)))` — both in the **grammar** (attribute slots on struct/union/members/bitfields from Phase 4 B2/B5 are a prerequisite; the layout info must be *retained* through `TypeVisitor`, not discarded like today's attributes) and in the **logic** (offset/size/padding computation per architecture data model ILP32/LP64).
   - This encoding **forces bitvector arithmetic** for the whole program (extraction is meaningless over mathematical ints). Activation policy: **if unions are present → this encoding is the default** (only sound way to model type punning); **if only fixed-size arrays/structs exist → opt-in** via new `FrontendConfig` option **`--enable-bitvectors-for-objects`**.
   - Interaction to watch: forcing bitvector mode collides with the overflow pass unless Phase 5's bitvector `LimitVisitor` has landed — sequence Phase 5 before enabling this for no-overflow tasks.
   - Scope note: this subsumes parts of C11 (initializer handling for composite objects can be reworked on top of the flat bit-layout) — re-scope C11's remaining items once the design doc exists.
   - Test: layout unit tests (offsets/sizes for packed/aligned/bitfield cases, checked against gcc's `offsetof`/`sizeof` for the same structs), 26union.c type-punning fixtures with known verdicts, union-heavy families (ntdrivers, ECA, Huawei demo) spot-checks, and full canary sweep with the flag off (must be verdict-identical).
2. **C5 function pointers — candidate sets** (decision resolved) — 1,167 tasks (+ residue of B1). Implementation: fptr-typed variables (stop conflating with `isFunc()`), and an indirect-call dispatch pass lowering `(*fp)(args)` to a **switch over the candidate set** of address-taken functions with matching signature (nondeterministic choice guarded by `fp == &f_i`); calls where the candidate set is empty/unresolvable follow the N1 havoc-with-warning path. Test: 34fptr.c dispatch-table fixture with distinguishable verdicts per target; product-lines samples end-to-end after B1.
3. **N5 termination for recursive/non-inlineable programs (decision resolved: graceful unknown for now)** — replace the hard `error(...)` at `termination.kt:231-233` with a clean `unknown` result. Converts a big share of the 1,996 termination errors into unknowns (no score change, removes noise); full recursion support deferred.
4. **D7 portfolio (decision resolved: continue after clean `unknown`)** — a config *returning* `SafetyResult.unknown()` (no exception) currently short-circuits the whole chain (`stm.kt:152-173`); make the STM fall through to the next config on unknown results (27+ tasks). Also D4: frontend failure aborts before the portfolio exists — once frontend fixes land this matters less, but consider a "SimpleLts/degraded-frontend" fallback edge. Test: STM unit test — chain of two configs where the first returns unknown, assert the second runs; guard that a genuine Safe/Unsafe still stops the chain.
5. **Capability/performance** (11.6k timeouts): FLOAT portfolio tuning (worst correct:timeout ratio), ARR (array tasks currently crash-loop through KIND/PRED/NWT then timeout — see `data_structures_set_multi_proc` logs), NONLIN_INT. Separate benchmarking effort; propose after crash noise is gone so profiles are clean.

(W4 memory-model lifetimes moved fully into Phase 1.5 — implemented in `FrontendXcfaBuilder`, no residual Phase 6 work.)

---

## 4. Validation strategy (per phase and final)
1. **Unit level**: every fix has a fixture in `c2xcfa` tests (`./gradlew :xcfa:c2xcfa:test`) or `PassTests.kt`.
2. **Canary suite** (Phase 0.2): correctly-solved sub-60s tasks sampled from this run, stratified per sv-benchmarks subfolder, added to the integration tests with expected verdicts — run on every phase completion; any canary regression is a hard stop. (The existing `integration-tests/software/` suite is a smoke test only; the canaries are the real regression net.)
3. **Parse-only sweeps with `--backend NONE`** (Phase 0.3): cheap frontend-crash regression check over all canaries + per-category crash samples; mandatory after every grammar commit.
4. **Category spot-checks** (Phase 0.4 script): ≤15 sampled tasks per fixed category through the real archive; assert the crash signature is gone and no new wrong verdicts. Per-task expected verdicts are in the task `.yml`s.
5. **Wrong-result guard set** after every phase (13 wrong + neighbors): zero wrong verdicts tolerated (OC tasks now included — OC is in scope as of 2026-07-16).
6. **Final**: one full benchmark re-run (same infra as this run) after Phases 1-5; success criteria: wrong ≤ 4 (W5-class if unresolved), frontend-failure errors < 5,000 (from 17,570), no new wrong results, correct > 7,500 (from 5,917; conservative — Juliet/no-overflow/memcleanup alone should add ~1,000).

## 5. Architectural-decision register
Resolved (per review, 2026-07-09):
| ID | Decision | Resolution |
|---|---|---|
| AD1 (W2/1.3) | Signed-cast wraparound under integer arithmetic | **Resolved**: new `FrontendConfig` option `--enable-signed-wraparound` enabling modular wraparound; default off (signed wraparound is UB pre-C23) |
| AD3, AD4 (OC) | OC Unsafe guarding / OC on lowered properties | **BACK IN SCOPE (2026-07-16)** — the OC PR was merged into this branch; the concurrency/OC wrong results (see W6, ~60 `pthread-wmm` in the 2026-07-16 run) are now ours to fix here |
| AD5 (N1/Phase 3) | Unknown-extern semantics | **Resolved**: havoc all unresolved `InvokeLabel`s' return values + warning that side-effects may be swallowed |
| AD7 (C8/Phase 6) | Unions / composite objects | **Resolved**: model fixed-size arrays, structs, unions as large bitvectors with extraction-based access; honor `packed`/`aligned` in grammar and layout logic; forces bitvector encoding; default when unions present, otherwise opt-in via `--enable-bitvectors-for-objects` |
| — (C5/Phase 6) | Function-pointer lowering | **Resolved**: candidate-set dispatch |
| — (C4) | Addressable lvalues (`&a[i]`, `&s.f`) | **Removed from plan** — separate PR |
| — (N4) | Logger format crash | **Resolved**: fix misusing call sites; no skip-format shortcut in `BaseLogger` |
| — (N7) | Newton + `MemoryAssignStmt` | **Resolved**: encode WP/SP via array-store semantics instead of skipping |
| AD2 (W4/1.5) | Stack-lifetime tracking in memsafety model | **Resolved**: implement in `FrontendXcfaBuilder` (exact scope info still available), gated on the verified property demanding it |
| AD6 (B1/Phase 4) | Grammar casts | **Resolved**: `abstractDeclarator` unification, with `(expr)` vs `(type)` decided context-sensitively via the known type-name set (typedef feedback + semantic predicate); creative ambiguity test suite in the parsing submodule |
| AD8 (N5) | Termination + recursion | **Resolved**: graceful unknown for now, feature later |
| AD9 (D7) | Portfolio STM after clean `unknown` | **Resolved**: continue to the next config |
| AD10 (W2/1.3) | Who sets `--enable-signed-wraparound` | **Resolved**: nobody, currently — SV-COMP doesn't mandate modular signed semantics, and it would break overflow detection; add input-flag validation rejecting it together with the overflow property (+ test) |

**All architectural decisions are now resolved (2026-07-09). The plan is ready to execute.**

---

## Batch 65 — libvsync/OC: five fixes take the family from ~0 to 31/38 running (2026-07-27)

Executes the 2026-07-26 directive: *"run a benchmark with full 900 seconds of timeout for libvsync
only, with OC. Try the clocks/refinement config as well with MathSAT. If there are wrong results, or
exceptions/errors, go after them and repeat this until all libvsync tasks can at least be started in
all tested configs."*

**Baseline = run 67** (`Theta-svcomp-67`, `xmls/theta27-libvsync-oc3.xml`, 900 s, 3 decision
procedures x 2 properties = 6 rundefinitions, ~108 runs): **0 wrong** (good) but **52 ERROR / 27 OOM /
8 TIMEOUT / 0 correct**. Errors were near-identical across the three configs, i.e. config-independent
and therefore frontend/graph-construction bugs rather than solver ones. Failure sites:
`XcfaToEventGraph.exit:730` x24 and `LoopUnrollPass.getLoop:468` x9.

### Fixes (all validated against a local repro; canary 255 + 24 fixtures green, 0 FAIL)

1. **`LoopUnrollPass.kt` ~374 — `.reduce` -> `.reduceOrNull`.** A loop-condition location whose
   outgoing-edge list is empty made the loop-variable fold throw *"Empty collection can't be
   reduced"*. Hit caslock / hclhlock / ttaslock.
2. **`DataRaceToReachabilityPass.kt` — dereference flags are now per component type.** The four
   flags (`_deref_{array,offset}_{read,write}`) were hardcoded `IntType` behind
   `check(type == Int())`, which surfaced as a bare, message-less *"Check failed."* on arraylock /
   hclhlock / rwlock. Pointer components are **not** always Int (bitvector architectures and the
   non-default memory models produce BvType ones). Now one flag per `(kind, type)` via
   `derefFlagVar`, with a typed sentinel `noAccess(type)` (`Int(-1)`, or an all-ones Bv). The needed
   flags are discovered by scanning the whole `XcfaBuilder` **up front** (`derefFlags`) because they
   must exist before the init edge is constructed — they cannot be created lazily per procedure.
3. **`XcfaToEventGraph.kt` ~433 — a label-less outgoing edge is no longer rejected.** Such an edge is
   semantically `assume(true)`: it contributes no condition and the guard carries over unchanged,
   which is exactly what the traversal already did. The error message now names the offending label
   instead of being opaque. Hit hclhlock.
4. **`GlobalDeclUsageVisitor.java` — WRONG-RESULT bug, global, not OC-specific.**
   `visitGlobalDeclaration` overwrote an already-recorded function **definition** with a later bare
   **prototype** (via `usedContexts.replaceAll`) and wiped the usage set the body had recorded. The
   function became *undefined* -> havoc'd return value. Minimal repro:
   `static inline int helper(int x){return x+1;}` followed by `static inline int helper(int x);` and
   `if (helper(1) != 2) reach_error();` verdicts **Unsafe**; delete the prototype and it is Safe; gcc
   confirms no error is reachable. Preprocessed sources do this constantly, so the blast radius is
   far wider than libvsync — **this one needs a full benchmark, not just the libvsync run.** In
   libvsync it showed up as *"Unknown procedure: rec_{spinlock,ticketlock,mcslock}_acquire"*. Note
   `rec_` means **reentrant**, not recursive: these are ordinary inline functions and this was never
   an OC recursion limit. Fix: skip the declaration when an `ExternalFunctionDefinitionContext` is
   already recorded under that name (overwriting stays correct for redeclared *globals*, i.e. a
   tentative definition followed by the real initializer, which is what the branch was written for).
5. **`Builders.kt` `removeLocs` — edges and locations are kept in sync.** Found by the
   `checkEdgesHaveLocations` instrumentation added earlier this session (the user's "instrument the
   XcfaBuilders to find where we're inserting an edge without a proper location"); it fired under
   `--force-unroll` as *"SimplifyExprsPass left N edge(s) of procedure run attached to locations it
   no longer contains"*. `removeLocs` re-evaluated its predicate **while** unhooking edges, and the
   usual predicate asks whether a location has incoming edges — which the unhooking itself changes.
   So a location could leave `locs` with an edge still pointing at it. Now the match set is
   snapshotted per round and every edge **incident in either direction** to a removed location is
   dropped, unhooking both adjacency lists. Only caller is `UnusedLocRemovalPass`, whose predicate
   requires `incomingEdges.isEmpty()`, so the new target-side branch fires only in the corrupt case.

### Result

Local sweep, all 19 tasks x both properties (70 s cap): **31/38 configs now run** instead of
erroring. 7 errors remain, in 3 classes:

- **`loops` — MOSTLY FIXED (4 of 5) by two further changes.** Diagnosis came from making the error
  name the stuck locations and their incoming-edge deficits
  (`run_error_1[26/66], __loc_2664_loop1_1[1/2], ...`). Force unrolling leaves behind copies past
  the bound that nothing can reach, including whole **dead cycles**; every location in such a cycle
  has an incoming edge from within the cycle, so `UnusedLocRemovalPass`'s "no incoming edges" test
  kept them alive forever. They are invisible to the OC traversal but not to the incoming-edge
  *counts* it waits on, so a live merge point sat forever waiting for a predecessor that can never
  execute. Two changes:
  (a) **`UnusedLocRemovalPass` is now reachability-based** (reachable from `initLoc`) instead of
      predecessor-count based, which subsumes the old behaviour and also catches dead cycles;
  (b) **`XcfaOcChecker.check(i)` now runs `UnusedLocRemovalPass` after `LoopUnrollPass`** — the OC
      path built its pass manager with `LoopUnrollPass` *alone*, so no dead-code removal ran there
      at all. This was the actual blocker; (a) alone changed nothing on the OC path.
  Also rewrote **`LoopUnrollPass.findBackEdge` as a proper three-colour DFS**: the old one marked
  edges explored globally, so a back edge first reached along a path not through its target was
  never recognised. That did not fix these tasks but is a real latent-correctness bug.
  Result: ticketlock, cnalock, hemlock, ttaslock now build their event graph and verify in both
  properties. **`caslock-race` still reports `loops`** — its `run_error` deficit dropped from
  `[21/156]` to `[21/92]`, so dead code was genuinely removed but one *reachable* cycle survives
  `cutRemainingBackEdges`; that residue is the remaining lead. Note `count()` deliberately bails on
  loops whose edges carry dereferences (guard added earlier to stop a Z3 crash on derefs lacking
  `uniquenessIdx`), which is precisely the shape of a spin loop.

  **`--force-unroll` is not the answer for this class.** It does get all ten configs past graph
  construction, but it sets `unsafeUnroll`, and `XcfaOcChecker` correctly refuses a Safe verdict
  that used an incomplete bound and escalates. ticketlock / cnalock / ttaslock are expected
  **true** on both properties, so Safe is unreachable and they would merely turn from errors into
  timeouts; only caslock and hemlock (expected **false**) could gain. No wrong-result risk either
  way, but no real win — a config tradeoff, not a fix.
- **`branching with non-assume labels` (2)** — bounded_mpmc_check_{empty,full}-race. Root cause
  traced: `AtomicReadsOneWritePass` localizes a deref flag that is written twice on one edge (the
  set/unset pair), and its copy-in (`_deref_array_read_Int_l35 := _deref_array_read_Int`) must
  precede a branch-guard assume that *reads the same flag*, so the existing `prefix` guard (leading
  assumes must not touch a localized var) computes 0 and the copy-in lands first.

  **Design constraint for whoever fixes this — two tempting fixes are both unsound:**
  1. *Relaxing OC's `firstLabel`* to mean "first assume" rather than "first label" skips populating
     `assumeConsts`, so the "constants in the different branches must be equal" constraints
     (`XcfaToEventGraph` ~line 440) are never emitted and sibling branches may read different
     values of the same global.
  2. *Hoisting the copy-in above the branching location for only the edge that needs it* has the
     same effect by a different route: that branch's assume then references the local `_lNN` while
     its siblings still reference the global, so the `assumeConsts` key differs and the branches are
     again untied.

  The hoist is only correct if it covers **every** outgoing edge of the branching location and they
  all share **one** local per variable: then there is a single read of the global, every sibling
  assume references that same local, and `assumeConsts` ties them as before. That means
  `localVersions` must be computed per *branching location* rather than per edge (today it is
  per-edge, `AtomicReadsOneWritePass` ~line 84), with a new location inserted so the copy-in edge
  sits above the branch. Correctness-critical: this is the data-race path, so a subtle error here
  produces silent wrong race verdicts, not a crash.
- **`OC checker requires function inlining: init` (1)** — hmcslock-unreach. **Inherent, not a bug:**
  `hmcslock_acquire_real(lock->parent, &lock->qnode, depth - 1)` is genuinely recursive, so
  `canInline()` marks the caller non-inlinable and OC requires full inlining. (Secondary
  observation: `canInline` is all-or-nothing per caller, so one recursive callee blocks inlining of
  every other call in that procedure, including the perfectly inlinable `init` — worth improving,
  but it would not unblock this task.) hmcslock-**race** does now run.

### Measurement caveat — local sweeps UNDER-REPORT errors

A local sweep with a short per-task cap is not a reliable error count. These OC failures happen at
graph construction, i.e. deterministically and early *in the run*, but a run under heavy local
parallelism (8-10 concurrent JVMs at `-Xmx8g` on a 24-core box) may not have reached graph
construction by the cap, and then shows as "still running" rather than as the error it will
deterministically produce. Confirmed on `ttaslock-unreach`: it appeared clean in one sweep, yet a
direct single run fails at the very first unroll bound every time. So treat local sweep numbers as
a *lower bound* on the error count; only the 900 s benchmark on dedicated vcloud cores is
authoritative.

### Process note (cost a discarded canary run)

Never rebuild / re-extract `subprojects/xcfa/xcfa-cli/build/distributions/Theta-svcomp` while a
canary sweep or local sweep is in flight — they execute out of that exact directory, so the `rm -rf`
lands mid-run and silently invalidates the results.


## Batch 66 — libvsync/OC runs 68 and 69: errors cut 65%, but the family still yields no verdicts (2026-07-27)

Two 900 s libvsync-only OC benchmarks on sosy, same `xmls/theta27-libvsync-oc3.xml` (87 runs, 3
decision procedures x 2 properties). Run 68 = Batch 65 fixes 1-5; run 69 = all 8.

| | run 67 (baseline) | run 68 (fixes 1-5) | run 69 (all 8) |
|---|---|---|---|
| ERROR | 52 | 36 | **18** |
| OUT OF MEMORY | 27 | 35 | **48** |
| TIMEOUT | 8 | 16 | **21** |
| correct | 0 | 0 | **0** |
| **wrong** | **0** | **0** | **0** |

**What the fixes achieved.** Every error class targeted in Batch 65 is gone from the real
benchmark: "Empty collection can't be reduced", the bare "Check failed.", and "Unknown procedure:
rec_*" do not appear in run 68 or 69, and the dead-cycle fix removed the loops errors for cnalock,
hclhlock, ticketlock, mcslock and rec_mcslock in run 69. Errors fell 52 -> 18 (-65%), and no wrong
result was introduced at any point.

**What they did NOT achieve, and this is the honest headline: the libvsync family still produces
zero verdicts.** Every error removed became an OOM or a TIMEOUT, not a `correct`. OOM is now the
dominant outcome (48 of 87, up from 27), which says the OC event graphs for these locks simply do
not fit the 7 GB limit. That is a scaling problem, distinct from the frontend/graph-construction
bugs fixed here, and it is what actually gates any score from this family. Chasing the last error
classes has low marginal value until it is addressed.

**Remaining 18 errors = 6 task-configs x 3 solver configs** (identical in all three, i.e. still
config-independent):
- `loops` (6): **caslock-race**, **ttaslock-unreach** only. One reachable cycle survives
  `cutRemainingBackEdges`; see Batch 65 for the diagnostic that localises it.
- `branching with non-assume labels` (6): **bounded_mpmc_check_full-race**, **bounded_spsc-race**.
  Fix design and the two unsound shortcuts are recorded in Batch 65.
- `OC checker requires function inlining` (6): **hmcslock** both properties — inherent,
  `hmcslock_acquire_real` genuinely recurses and OC requires full inlining.

Artifacts: `scratchpad/r68`, `scratchpad/r69` (logfiles + per-config result XMLs).


## Batch 67 — the last two tractable OC error classes, root-caused and fixed (2026-07-27)

Follow-up to Batch 66's 18 remaining errors (6 task-configs x 3 decision procedures). Two of the
three classes are now fixed; the third is inherent.

### `loops` (6 runs: caslock-race, ttaslock-unreach) — FIXED. Stray location twins.

Earlier entries called this "a reachable cycle surviving `cutRemainingBackEdges`". That was wrong.
The real mechanism:

`LoopUnrollPass.copyBody` names each copied location `${name}_loop${index}`. That name is **not
unique** -- copying the same region again in a later round, which nested loops do, regenerates a
name the procedure already holds. `XcfaProcedureBuilder.addLoc` is a silent no-op for a location it
already has, but `copyBody` kept handing out the *stray instance* it had just constructed. Because
`XcfaLocation` is a **data class** (structural equality on name/flags/metadata), edges built from
that twin still satisfy `addEdge`'s `toAdd.target in locs` check -- while the twin owns its own,
empty `incomingEdges`/`outgoingEdges` sets.

Consequences, in order of how they hid the bug:
1. Every adjacency-walking traversal is blind to those edges. That includes `findBackEdge`, so the
   pass's own back-edge cut saw an acyclic graph and cut nothing.
2. `XcfaProcedure.deepCopy` resolves endpoints through a map keyed by *equality*, so it re-points
   the edges onto the registered instance. The cycle therefore materialises only in the per-thread
   copy -- which is precisely where the OC checker reported "loops".
3. `checkEdgesHaveLocations` (the instrumentation added earlier this session) missed it because it
   tested membership with `in`, i.e. by equality. **Making that check identity-based named the
   offending pass immediately** and is kept: it is a strictly better invariant.

Fix: disambiguate the copied name only on an actual clash, so the usual names stay stable --
`PassTests` asserts on them, and an unconditional counter suffix broke that test.

### `branching with non-assume labels` (6 runs: bounded_mpmc_check_full-race, bounded_spsc-race) — FIXED.

Implemented the hoist design recorded in Batch 65. `AtomicReadsOneWritePass` now detects a branching
location where some outgoing edge's *leading guard* reads a variable that must be localized (so the
old `prefix` mitigation computes 0), and inserts a new location above the branch carrying a single
`local := global` copy-in. **Every** sibling edge is then rewritten to read that shared local.

Covering all siblings is the part that makes it sound: OC ties sibling branch conditions together
through the declaration they read (`assumeConsts` in `XcfaToEventGraph`), so localizing only the
edge that needs it unties them and lets two branches disagree about the value of the same global --
a false race, not a crash. The write-back is emitted only on branches that actually modify the
local; an unconditional one would add a spurious write event to the global on the read-only branch.

This matches exactly what `DataRaceToReachabilityPass` produces: `assume(assertion); set; access;
unset` on the MAIN_PATH edge (flag written twice -> `wrongWrite`) against `assume(!assertion)` on
the ALTERNATIVE_PATH sibling, which only reads the same flags.

### `OC checker requires function inlining` (6 runs: hmcslock, both properties) — INHERENT.

`hmcslock_acquire_real(lock->parent, &lock->qnode, depth - 1)` is genuinely recursive and OC
requires full inlining. The recursion depth *is* bounded by a constant (`num_levels = 3`), so
bounded recursive inlining would unblock it -- that is a feature, not a fix, and is not attempted.

### Validation

696 unit tests, 255 parse canaries + 24 fixtures, and -- because the branching fix is on the
data-race path, where a mistake yields wrong race verdicts rather than a crash -- **all 30
`no-data-race` canaries re-run in full verdict mode: 30/30 PASS**.

### Expected payoff: errors 18 -> 6, score unchanged

Runs 68 and 69 both showed every removed error becoming an OOM or TIMEOUT, never a `correct`. These
12 will very likely do the same. The OOM wall (48 of 87 runs in run 69) remains the binding
constraint for this family; it is a scaling problem in the OC event-graph encoding, not an error
class, and no amount of further error-chasing will produce a verdict here without addressing it.


## Batch 68 — run 70 result: libvsync error chase COMPLETE (2026-07-27)

`Theta-svcomp-70`, same `xmls/theta27-libvsync-oc3.xml` (87 runs, 900 s, 3 decision procedures x 2
properties). Full progression of the chase:

| | run 67 | run 68 | run 69 | **run 70** |
|---|---|---|---|---|
| ERROR | 52 | 36 | 18 | **6** |
| OUT OF MEMORY | 27 | 35 | 48 | **57** |
| TIMEOUT | 8 | 16 | 21 | **24** |
| correct | 0 | 0 | 0 | **0** |
| **wrong** | **0** | **0** | **0** | **0** |

**Errors down 88% (52 -> 6), zero wrong results at every step.** The only remaining errors are
`hmcslock` in all six configs -- the inherent recursion case (`hmcslock_acquire_real` recurses on
`lock->parent`; OC requires full inlining). 18 of 19 libvsync tasks now start in every tested
config, which closes the "every libvsync task at least starts" directive apart from that one.

**And the predicted null result held exactly: the score did not move.** Every error removed across
runs 68-70 became an OOM or a TIMEOUT; not one became a `correct`. OOM is now 57 of 87 runs (66%,
up from 27 at the start). This is the honest conclusion of the whole exercise:

> The libvsync family produces **zero verdicts**, and the binding constraint is that the OC event
> graph for these locks does not fit in 7 GB. That is a scaling property of the encoding, not an
> error class. No further error-chasing can produce a score here; the next real step for this
> family is the memory footprint of `XcfaToEventGraph` (or a larger memlimit), not more frontend or
> graph-construction fixes.

Ten fixes landed across Batches 65-67 to get here. Their durable value is not the libvsync score
(there is none) but the general bugs found along the way -- above all the
prototype-after-definition **wrong-result** bug (Batch 65 fix 4), which is global and still wants a
full `theta27-short` run before it is trusted.


## Batch 69 — `--force-unroll-recursion`: expand recursive calls at the force-unroll bound (2026-07-27)

Per the user's design: a setting that unrolls call invocations to the same degree as force
unrolling, wired into **`LoopUnrollPass`, not `InlineProceduresPass`**, so it is re-applied when the
bound increases -- and with the inlining machinery factored into shared utilities.

### Structure

New `ProcedureInlining.kt` holds what both callers need: `inlineCallSite`, `inlinedCopy`,
`callsKnownProcedure`, `calleeOf`, `recursiveProcedureNames`, and a `ProcedureBody` snapshot type.
`InlineProceduresPass` now delegates to it and is otherwise unchanged (verified as a pure refactor:
unit tests green before the new feature was added). `LoopUnrollPass.unrollRecursiveCalls` runs
*before* the loop search (a spliced body brings its own loops) and is gated on
`--force-unroll-recursion`; `XcfaOcChecker` passes `parseContext` so the splice can build the
parameter assignments. Because the pass runs per force-unroll bound, each escalation expands the
recursion one level deeper -- which a one-shot inlining pass cannot do.

### Three bugs the design flushed out, all producing WRONG VERDICTS rather than crashes

1. **Self-recursion aliases caller and callee.** `callee === builder`, so walking the callee's edges
   while adding to the builder threw `ConcurrentModificationException`.
2. **The snapshot was taken after the call edge had been removed**, so the spliced body no longer
   contained the recursive call. Recursion was silently truncated to a single level -- no cut, no
   `unsafeUnroll`, and a confident wrong answer. Fixed by capturing every body at the start of a
   round, before anything is spliced (`ProcedureBody`).
3. **Nested frames shared variable declarations.** Every spliced copy reused the callee's decls, so
   the inner `sum(n-1)` wrote the very `n` its caller was still using and the outer guards read the
   innermost value. Verdicts were wrong in *both* directions. Fixed with a per-expansion frame
   (`_inlNN` renaming through `changeVars`), requested via `inlineCallSite(freshFrame = true)`.

Also replaced `canInline()` as the recursion test: it caches in `metaData` and conflates "is
recursive" with "reaches recursion", so once bodies start mutating it gives order-dependent answers
(it reported the plainly self-recursive `sum` as non-recursive). `recursiveProcedureNames` computes
it from the call graph, settled once per pass instance.

### What it does and does not achieve

- **Bug-finding works.** `int sum(int n){ if (n<=0) return 0; return n + sum(n-1); }` with
  `sum(3) != 5` -> **Unsafe** (correct) at bound 2.
- **Proving safety of a recursive program does not terminate.** With `sum(3) != 6` the checker
  escalates 2,3,4,5,6,7... indefinitely: at every bound a call site *structurally* remains (inside
  the base-case copy), so the cut fires, `unsafeUnroll` stays set, and the checker correctly refuses
  the bound-limited `safe`. Recognising that the remaining call is *semantically* unreachable needs
  reasoning bounded unrolling does not have -- the same reason BMC cannot prove loop safety. With
  `forceUnrollBoundEnd = -1` this is an unbounded escalation, i.e. a timeout in practice.
- **hmcslock** now clears the `requires function inlining` barrier and stops on a *different*,
  pre-existing OC restriction: `variable (var t0::hmcslock_init_ret_inl14150 Int) is not
  initialized` (`XcfaToEventGraph.addCrossThreadRelations`). A void callee never writes its
  frontend-invented `_ret` variable, so the caller's write-back reads something OC considers
  uninitialized. `InlineProceduresPass` has always had this shape; hmcslock simply never got far
  enough to hit it. Fixing it means initialising the spliced frame's OUT params at the call site --
  not attempted here.

### Open policy question for the user

Should `--force-unroll-recursion` respect `forceUnrollBoundEnd` so a safe recursive program ends as
`unknown` instead of running out the clock? That changes escalation semantics, so it was left alone.

### Validation

Off by default (`LoopUnrollPass.UNROLL_RECURSION = false`) and verified inert -- without the flag
the recursive test still reports `requires function inlining`. 696 unit tests, 255 parse canaries +
24 fixtures, all green.


## Batch 70 — run 72 triage: frontend failures and propagator wrong results (2026-07-27)

Run 72 = full concurrency set, 5 OC configs x 4 properties, 15,880 runs. Headline numbers are in the
session notes; this entry records the bugs found and fixed from it.

### Frontend failures: 562 per config (2,810 runs, 17.7%), config-independent

Root causes, by share: `CLibraryFunctionsPass` 397 (71%) -- non-constant deref offset in a library
arg 226, local (non-global) mutex handle 139, lib arg not a reference base 32 -- then
`ExpressionVisitor` 115, and a tail of ~50.

**Fixed (108 of 562):**
1. **"No such variable or macro: <function>" (81).** Not a missing symbol -- an *ordering* bug.
   `GlobalDeclUsageVisitor` keeps a redeclared global at its *original* position while adopting the
   later context, so `int (*p)(void); ... int (*p)(void) = f;` evaluates the initializer long before
   `f` is reached. Fix: introduce every function's name before any global declaration is processed.
   **Watch out:** the variable must also be registered in `FunctionVisitor.functions`, or
   `registerIfFunctionUsedAsValue` no longer recognises an address-taken function and every one of
   them loses its id and initial value -- caught by `FunctionPointerReturnTypeTest`.
2. **"Only structs expected here" (27).** Also not where it appeared. `ThreadInfo.cell`, declared
   `Cell cell;`, resolved to `NamedType[int]`: the forward-typedef idiom
   `typedef struct Cell Cell; struct Cell {...};` hit `visitCompoundUsage`, whose bare map lookup
   returned **null** for a tag with no definition yet, and the specifier fell back to `int`, which
   the typedef froze. Fix: a `struct X` reference now *introduces the tag*, and the definition
   *completes that instance* instead of replacing it. A tag that already has fields still gets a
   fresh instance, preserving redefinition behaviour.

**Not fixed:** the `CLibraryFunctionsPass` mutex-handle family (397). All three of its errors are one
limitation -- *a pthread handle must resolve to one statically-named object* -- failing three ways:
index not constant (dominated by goblint's `pthread_t t[10000]` loops, 10x over `UNROLL_LIMIT`;
raising the limit is not the answer), object function-local, object reached through a struct field
or pointer. `PthreadArrayHandleUnrollPass` also only triggers on `pthread_create`/`join`, so
`for (j...) pthread_mutex_lock(&mutex[j])` is never unrolled -- that part looks cheap.

### Propagator (baseline) wrong results: 19 -> 16

**Fixed:**
3. **`MemsafetyPass.annotateLost` (2 tasks: `singleton`, `singleton_with-uninit-problems`).** It
   checked only whether everything was *freed*, contradicting its own doc comment and SV-COMP's
   valid-memtrack ("pointed to OR deallocated" = Valgrind *definitely* lost). A block still named by
   a live global is now tracked. Locals are gone at the final location, so globals are the pointers
   that matter; a block reachable only *through* another heap block is not covered, which errs
   towards reporting a leak that is not one rather than missing one. **Backend-independent** -- the
   same false alarm existed on the CEGAR path.
4. **Integer limit macros (`04-mutex_17-ps_add1_nr`).** `MacroExprs` defined every limit as the C
   standard's *minimum guaranteed* magnitude -- the 16-bit ones: `INT_MAX` = 32767 where `int` is 32
   bits, `UINT_MAX` = 65535. So `if (i == INT_MAX) return;` compared against the wrong constant and
   left the real overflow reachable. Separately, the MIN values used `-MAX` instead of `-MAX-1`,
   ignoring two's-complement asymmetry (`INT_MIN` was -32767). All limits are now derived from the
   type's actual width. Also silently wrong before on LP64, where `LONG_MAX`/`ULONG_MAX` held ILP32
   values.

**Not fixed, with reasons:**
- **3 `popl20-*.wvr` race false alarms** -- atomicity arrives via a *cast on a malloc'd object*
  (`_Atomic int* arr = (_Atomic int*)malloc(...)`). Recorded earlier as deliberately deferred: the
  obvious fix (marking the object atomic) *hides* real races if the object is ever accessed plainly.
  Needs per-access atomicity, not a patch.
- **10 missed bugs.** `reorder_c11_good-{10..50}` (5) are the known C11 weak-memory gap.
  `09-regions_{03,05}` and `race-2_2b-container_of` need two heap cells reached through *different*
  pointer chains to be recognised as the same object (`A->next` and `B->next` both point at `p`,
  guarded by different mutexes) -- an aliasing-precision limit in the race check, not a localized
  bug. **Verified this is not a memory-model choice: `--memory-model flat` misses them too.**

### IDL: 63 missed bugs, unsound

Both IDL configs miss ~63 bugs against 6-10 for the others, and **57 are solved correctly by another
config** -- so it is neither task difficulty nor the solver, but the IDL decision procedure itself.
Concentrated in goblint `04-mutex`/`13-*` and `02-base` malloc-race families. Untouched; this is the
single largest correctness item outstanding.

### Validation

Every fix above: 255 parse canaries + 24 fixtures + full unit tests, 0 failures. The memsafety change
additionally re-ran the 18 memsafety canaries in **verdict mode** (16 PASS, 2 TIMEOUT, 0 FAIL),
because it *weakens* a check and could otherwise mask a real leak.


## Batch 71 — `pointsToAtomic` was never set for declared globals (2026-07-27)

Following the user's observation that "the result of the cast should have the atomic flag" for the
popl20/weaver race false alarms.

**Found and fixed.** `XcfaGlobalVar.pointsToAtomic` documents exactly the right notion -- *"The
object this points at is `_Atomic`: `_Atomic int *p` ... A different question from [atomic], and the
one a memory access has to ask"* -- but `FrontendXcfaBuilder.initializeGlobalVariable` never
populated it:

    XcfaGlobalVar(decl, type.nullValue, atomic = isAtomic)   // pointsToAtomic defaults to false

So `_Atomic int *A;` recorded that A itself is not atomic (right) and forgot that its *pointee* is.
It is now derived from the declared type (`CPointer`/`CArray` with an atomic element). Verified it
computes `pointeeAtomic=true` for `A`.

This is the **sound** form of the idea, and the distinction matters: it records the atomicity of the
*access path*, not of the object, so a second access to the same memory through a plain `int *` is
still race-checked. Marking the object atomic -- the variant rejected in earlier batches -- would
silently exclude it.

**It does not fix popl20**, and two follow-up attempts failed for the same underlying reason:
1. The `pointsToAtomic` branch in `XcfaDataRaceCheck.addressesAtomicData` needs the dereference's
   base to still be a `RefExpr` to the global. For heap memory it is not: by analysis time the base
   is the allocation's id, and a malloc'd object's base is a *runtime* value that can never be
   registered through `isAtomicObjectCell`.
2. Asking the *access's own* recorded C type (`A[i]` yields an `_Atomic int` lvalue) also fails --
   the metadata is keyed by object identity, so the passes that rebuild the expression lose it,
   which is the very reason `pointsToAtomic` exists as a stored flag. That attempt was reverted
   rather than left as unvalidated code in the race check.

**What closing popl20 actually needs:** the atomicity has to survive expression rebuilding -- either
by keeping the originating pointer on the dereference, or by marking the allocated object's cells
atomic when a pointer-to-atomic is assigned a fresh allocation. The second is the variant previously
flagged as risky, though the risk is narrower than first recorded: accessing an atomic object
through a non-atomic lvalue is UB in C, so for well-defined programs it is defensible. A design
call, not a patch.

Validation: 255 parse canaries + 24 fixtures + full unit tests, 0 failures.


## Batch 72 — atomic dereferences were never filtered in the race *transformation* (2026-07-27)

The user granted the assumption that no UB other than the checked property is reachable, which
removes the objection recorded in earlier batches against treating cast/declared atomicity as
authoritative. The actual gap turned out to be simpler and did not need that licence.

**`DataRaceToReachabilityPass` had no atomicity filtering for dereferences at all.**
`addressesAtomicData` lived only in `XcfaDataRaceCheck` -- the *native* race checker, which the OC
path (`--datarace-to-reachability`) does not use. Variables were filtered through
`potentialRacingVars`; dereferences never were. So every atomic heap access -- `_Atomic int *A;
A[i]++` -- was instrumented and reported as racing with itself.

Two changes:
1. **Extracted** the resolution into `xcfa/utils/AtomicAccessUtils.kt` (`addressesAtomicData`,
   `resolveObjectBase`, `asConstantBigInteger`), parameterised on the global-var collection.
   `XcfaDataRaceCheck` delegates to it -- no duplicate copy.
2. **`DataRaceToReachabilityPass` filters atomic dereferences** with it. Needed a `ParseContext`,
   which meant updating three other construction sites (two passed `enabled` positionally, plus a
   unit test) -- all caught at compile time.

Together with Batch 71 (`pointsToAtomic` now set from the declared type) the chain works end to end:
the declaration records that the pointee is atomic, and the transformation consults it.

Verified discriminating: `_Atomic int *A` + malloc, two threads on `A[0]` -> **Safe**; the same with
a plain `int *` -> **Unsafe** (real race still caught); and the full popl20 shape -- a helper
returning `(_Atomic int*)malloc(...)`, loops, two threads -> **Safe**.

**Gate: 30/30 data-race canaries in verdict mode**, plus 255 parse canaries + 24 fixtures and full
unit tests. That verdict run is the one that matters, since this change *suppresses* race reports.
The three real `popl20-*.wvr` tasks get past the frontend but do not finish in 800 s locally, which
is consistent with the spurious counterexample being gone (proving safety is harder than finding a
false race) but is not proof -- the benchmark will confirm.

## Missed races: a 15-line reproducer for the `09-regions` class

Not fixed, but reduced from a 60-line benchmark to this, which is the useful artefact:

    struct s { int datum; struct s *next; } *A, *B;
    // main: p = malloc(...); A = malloc(...); A->next = p; B = malloc(...); B->next = p;
    // thread: lock(m1); A->next->datum++; unlock(m1);
    // main:   lock(m2); B->next->datum++; unlock(m2);      // RACE: same cell, different mutexes

Bisected precisely:
- `(*p)++` in both, different mutexes  -> **Unsafe** (correct: the core mechanism works)
- `(*p)++` in both, same mutex         -> **Safe** (correct)
- `A->next->datum++` in *both*         -> **Unsafe** (correct)
- `A->next` vs `B->next` (they alias)  -> **Safe** (MISSED)
- same, but each loaded to a local first -> **Safe** (MISSED)

So the miss is specifically *two different pointer chains that alias at runtime*; it is not about
nesting per se, since the identical-chain case is caught. Note the points-to analysis
(`xcfa.pointsToGraph`) feeds only COI and POR, not the race path, so the alias graph is not the
filter. This is pre-existing -- it is `09-regions_03-list2_rc` in run 72 -- and unaffected by any of
today's changes.


## Batch 73 — run 77: three low-hanging fixes, propagator 1515 -> 1721 correct, ZERO false alarms (2026-07-28)

Run 77 = same benchmark as run 72 (Concurrency set, 5 OC configs x 4 properties, 15,880 runs,
15 GB / 2 cores / 900 s) with the session's fixes, and **CPU-pinned** this time.

### Propagator baseline, run 72 -> run 77

| outcome | 72 | 77 | delta |
|---|---|---|---|
| correct | 1515 | **1721** | **+206** |
| server error | 290 | **83** | **-207** |
| frontend failure | 562 | 542 | -20 |
| timeout | 671 | 695 | +24 |
| out of memory | 98 | 103 | +5 |
| **wrong** | 19 | **10** | **-9** |

**All nine false alarms are gone; the remaining 10 wrong are exactly the missed bugs** identified
earlier and not fixed: `reorder_c11_good-{10..50}` (5), `race-2_2*-container_of` (2),
`09-regions_{03,05}` races (2), `09-regions_09-arraylist-deref` memsafety (1).

All five configs: propagator 1515->1721, refinement_z3 1491->1698, refinement_mathsat 1484->1651,
idl_z3 1426->1614, **idl_mathsat 1162->1157 (the only regression)**. Wrong counts: propagator
19->10, refinement_z3 14->8, refinement_mathsat 12->8, idl_z3 66->64, idl_mathsat 63->63 — the IDL
missed-bug count is untouched at ~63 and is now unambiguously the largest correctness item.

### The three fixes

1. **Terminal-sink exemption (the big one).** ~220 of the 233 memsafety "server errors" were one
   cause: *"incoming paths disagree on atomic nesting"* at thread **final** locations.
   `MemsafetyPass.breakUpErrors` redirects error edges into the final location, so it collects both
   ordinary completion and paths that were inside a locked region. Execution stops there, so no
   later event exists for an atomic context to govern. `isErrorSink` generalised to
   `isTerminalSink` (also `final`, or no outgoing edges). Memsafety alone went 185 -> 390 correct.
2. **`PthreadArrayHandleUnrollPass` trigger set** extended to the mutex/condvar handle functions.
3. **`asConstant()` simplifies** before matching a literal, so `(mod 4 4294967296)` counts.

### Why the frontend total only moved 20 — layered barriers, not independent buckets

Both parse fixes worked exactly as projected: `no such variable/macro` **88 -> 7**,
`only structs expected` **27 -> 0**. That is the 108 runs predicted. But the net is only -20,
because the same tasks then stop at the *next* construct in the same file, some of it newly
reachable code:

| bucket | 72 | 77 |
|---|---|---|
| ExprVisitor: no such variable/macro | 88 | **7** |
| ExprVisitor: only structs expected | 27 | **0** |
| other: getrExpression | 0 | **68** (new) |
| CLibFn: local mutex handle | 139 | 152 |
| FrontendBuilder: pointer arithmetic | 3 | 11 |
| other: handleUnsignedConversion | 0 | 8 (new) |
| other: structMemberAccess | 0 | 4 (new) |

Zero *new* frontend failures among tasks that previously parsed, so nothing regressed. **Lesson for
estimating: removing a frontend barrier is not the same as gaining a verdict** — the driver families
need several fixes each. The memsafety fix converted cleanly precisely because those tasks already
parsed and only the OC check rejected them.

Also visible: `non-constant deref offset` 226 -> 213 (-13) with `local mutex handle` +13 — the
mutex-array unroll works and hands those tasks to the local-mutex-handle barrier.

### Retracted: local mutex handles (was listed as low-hanging)

`MutexToVarPass` keys mutex identity by **name** (`_mutex_flag_<name>`) and runs *before* per-thread
copying, so allowing a function-local mutex would give two threads running the same function one
shared flag for two independent locks. That serialises them and **hides races**. It needs
per-thread-instance mutex identity; not a one-line relaxation.

Validation: 255 parse canaries + 24 fixtures, 30/30 race verdict canaries, memsafety verdict
canaries 16 -> **17** PASS, full unit tests — 0 failures.

## Batch 74 — C11 reordering races; and what the run-78 "regressions" actually are (2026-07-28)

Two separate things: a **real soundness fix** (`reorder_c11_good-*`), and the **attribution of the
64 portfolio regressions** in run 78 vs batch 61, which are mostly not defects.

### Fix: constant folding erased the racing reads (`reorder_c11_good-{10,20,30,40,50}`)

All 5 were missed bugs (expected `false(no-data-race)`, we said Safe). The task shape:

```c
static void *setThread(void *p)   { __VERIFIER_atomic_begin(); a = 1;  __VERIFIER_atomic_end(); ... }
static void *checkThread(void *p) { if ((a == 0 && b == 0) || (a == 1 && b == -1) || 1) ; else ERROR; }
```

`setThread` writes `a`/`b` inside atomic sections; `checkThread` reads them **unprotected**. Atomic
sections create no happens-before edge, so those conflict — a real race.

Three minimal variants isolated the cause (atomic sections are a red herring):

| variant | `\|\| 1` | atomic sections | verdict |
|---|---|---|---|
| A = benchmark shape | yes | yes | **Safe** (the missed bug) |
| B | **no** | yes | **Unsafe** (race found) |
| C | yes | **no** | **Safe** |

`ExprUtils.simplify` folds `X \|\| Y \|\| 1` to `true`, which erases the reads of `a` and `b`
inside it. Sound for reachability; fatal for data race — the conflicting access simply stops
existing. `SimplifyExprsPass` runs at `ProcedurePassManager` lines 68/98/123, all **before**
`DataRaceToReachabilityPass` (126).

Fix: under `inputProperty == DATA_RACE`, keep the original label when simplification would drop a
shared access. Precedent: the pass already bails out entirely for `OVERFLOW`.

⚠️ **The guard must apply to assumes only.** The first attempt guarded every label and broke
`09atomicfield_norace` (a *false alarm* on an `_Atomic` field) — caught by `XcfaDataRaceTest`.
Simplification also **rewrites** a dereference's address expression, folding `base + offset` to a
constant, and that fold is exactly what lets the atomic-cell check resolve the object base. A
rewrite drops the old global var *and* the old `Dereference` key from the label without dropping
the access, so no access-set comparison can tell "rewritten" from "removed". Assumes don't need
address folding, so scoping the guard to them keeps both behaviours. Comparing dereferences by
*count* instead of identity was also tried and still failed — the global var `s` is lost too.

Validation: 5/5 real tasks now `Unsafe`; 255 parse canaries + 24 fixtures; **30/30 race verdict
canaries**; memcleanup 1/1; 433 unit tests, 0 failures.

### The 64 run-78 regressions vs batch 61 are mostly NOT defects

| property | n | shape |
|---|---|---|
| valid-memcleanup | 16 | verdict lost — the CWE401 memtrack-exemption bug, already fixed + gated |
| termination | 16 | 6 OOM + 10 TIMEOUT |
| unreach-call | 16 | 15 TIMEOUT + 1 OOM |
| valid-memsafety | 8 | 7 TIMEOUT + 1 unknown |
| no-overflow | 6 | TIMEOUT |
| no-data-race | 1 | TIMEOUT |

**34 of the 49 resource regressions were already >150s in batch 61** against a 300s limit — margin,
not mechanism. Local master-vs-ours runs on the fast ones:

| task | master | ours | verdict |
|---|---|---|---|
| `45_monabsex1_vs` | 7.0s / 0.37GB | **120.4s / 1.69GB** | both **Safe** |
| `46_monabsex2_vs` | 6.9s | **125.8s** | both **Safe** |
| `id_build.i.p+sep-reducer` | 13.7s | **107.6s** | both **Safe** |
| `mannadiv_unwindbound10` | TIMEOUT | 74.7s | ours **Unsafe** (better) |

**No correctness regression anywhere** — every task ours completes gives the same or a better
verdict. Cause, straight from the logs: master's OC stage **crashes instantly**
(`IllegalStateException` at `XcfaToEventGraph.kt:232`, exit 202) and falls through to a config that
solves the task in ~3.5s; our OC fixes removed that crash, so OC now genuinely runs to its
`timeoutMs = 250_000` (exit 201) first. That is the *cost of the fix*, not a new defect.

⚠️ **The portfolio timeouts are tuned for SV-COMP's real 900s budget, not our 300s benchmark.**
`multithread.kt`: OC 250s, EXPL_SEQ_ITP 300s, PRED_BW 320s, PRED_SEQ_ITP 750s. Under
`theta27-short.xml` (`timelimit="5 min"`) OC alone eats 83% of the budget; at 900s it is ~28% and
the fall-through still has ~650s. Locally ours *does* finish (wall 267s, Safe). **Do not retune the
portfolio to the short benchmark** — that optimises the proxy, not the target. The open question is
whether to benchmark at 900s instead.

### Two measurement traps (both faked results before being caught)

1. **Upstream master is not a valid baseline for the portfolio.** It `Frontend failed!`s in 1.4-3.0s
   on the entire termination + product-lines set (`*_cilled_*`, `email_spec*`, `elevator_*`) — those
   tasks only became solvable in our own line of work. Baseline = batch 61. Master is valid only for
   the OC/concurrency configs.
2. **This container is capped at 8 GB** (`/sys/fs/cgroup/memory.max`); `free` reports the TrueNAS
   host's ~62 GB. `theta-start.sh` hardcodes `-Xmx14210m`, so 4 parallel local runs get SIGKILLed at
   ~2 GB RSS (rc=137) — indistinguishable from a real OOM regression — and `./gradlew test` dies with
   `Test Executor ... exit value 137`, which is the OOM killer, *not* a test failure. Run one theta
   at a time; `--max-workers=1` for tests.

Run 79 (this build, all fixes) launched on sosy pinned to `5750G` — the same CPU model batch 61 used,
so the comparison is clean.

### Batch 74 addendum — serial batch-61-vs-now comparison (the authoritative numbers)

Re-run **serially** (the 8 GB cgroup makes parallel local runs worthless, see above), batch 61's
build vs the current one, same host:

| task | property | b61 | now | x | verdict |
|---|---|---|---|---|---|
| `46_monabsex2_vs` | memsafety | 5.9s | 414.5s | **70x** | Safe (same) |
| `45_monabsex1_vs` | memsafety | 6.9s | 398.4s | **58x** | Safe (same) |
| `43_1a_cilled…plusb` | termination | 11.9s | 113.6s | 9.5x | Unsafe (same) |
| `id_build.i.p+nlh-reducer` | unreach | 17.1s | 160.1s | 9.4x | Safe (same) |
| `32_1_cilled…empeg` | termination | 13.5s | 113.2s | 8.4x | Unsafe (same) |
| `id_build.i.p+sep-reducer` | unreach | 17.7s | 140.9s | 8.0x | Safe (same) |
| `email_spec3_product27` | termination | 117.9s | 120.6s | 1.0x | Safe (same) |
| `email_spec27_product28` | termination | 90.0s | 91.6s | 1.0x | Safe (same) |
| `cast_float_ptr` | unreach | 23.4s | 23.5s | 1.0x | same (both TIMEOUT) |
| `mannadiv_unwindbound10` | unreach | 70.6s | 69.9s | 1.0x | Unsafe (same) |

**Every verdict is unchanged — the regressions are purely performance.**

⚠️ **Corrects the parallel-run reading above.** The product-lines "OOM cluster" does **not** regress:
`email_spec27_product28`, flagged as the most suspicious memory jump (1.88 GB -> OOM in run 78), is
identical on both builds serially and returns Safe. Those run-78 OOMs were benchexec-side variance.
4 of the 10 tasks do not regress at all, so this is **not** a broad slowdown — and `cast_float_ptr`
TIMEOUTs on batch 61 too, so its batch-61 "correct" was itself marginal.

Two mechanisms among the 6 that do regress:

1. **`45`/`46_monabsex*` (58-70x)** — the OC budget mechanism above: OC used to crash out instantly,
   now runs to its 250s timeout before the fall-through solves the task.
2. **The 8-9.5x group** — mechanism **not identified**. Ruled out *by measurement*: recursion
   unrolling (`forceUnroll=-1`, so it never triggers), frontend/parse time (identical, 1.7s), config
   path (identical), alias graph (identical, `9 -> [1,1,…]`), and `checkEdgesHaveLocations` (runs
   once per pass, not per edge — far too cheap). A function-pointer-precision hypothesis was
   **discarded**: the alias graph is byte-identical between builds.
   Supported-but-unconfirmed suspect: the `LoopUnrollPass` determinism/back-edge changes — the
   regressing tasks are exactly the loop-heavy ones (LDV drivers, loop-invgen reducers) while the
   unaffected sequential tasks are small.

## Batch 75 — run 79 (all fixes) vs batch 61: score +155, and a newly-exposed false-alarm family (2026-07-28)

Run 79 = current `svcomp27-fixes` build (through `865dc7607c`), `theta27-short.xml`, pinned to
`5750G` — the same CPU model batch 61 used. Real & complete: 55 XMLs, 0 `Cannot start process`,
tmux gone, 13:13 -> 19:28 (~6.25h). Downloaded to `results-2026-07-28_13-13-run79/`.

| category | batch 61 | run 79 | Δ |
|---|---|---|---|
| correct | 10,424 | 10,861 | **+437** |
| wrong | 41 | 83 | **+42** |
| error | 25,769 | 25,308 | −461 |
| unknown | 368 | 350 | −18 |
| **score** | **16,320** | **16,475** | **+155** |

Transitions: `error->correct` 455, `unknown->correct` 21, `wrong->correct` 7; `error->wrong` **51**,
`correct->error` 45.

### The 46 lost-correct are ALL resource — the accepted performance regression

31 TIMEOUT + 14 OOM + 1 unknown, **zero** wrong verdicts. Termination is the worst hit (23 lost: 13
OOM, 10 timeout), matching the 8-9.5x slowdown measured on `*_cilled_*` in the batch-74 addendum.
So the perf regression costs ~46 correct results; the fixes still net +437.

### 51 new wrong = 46 false alarms + 5 missed bugs, and one family dominates

| family | n |
|---|---|
| `cstr*` / `openbsd*` alloca-string | **30** |
| `aws_*` harnesses | 6 |
| `*_cilled_*` LDV (termination) | 2 |
| assorted singletons | 13 |

By property: valid-memsafety **36**, unreach-call 7, no-overflow 4, no-data-race 2, termination 2.

⚠️ **These are not new defects — they are old ones the frontend errors were hiding.** Almost every
one was `ERROR (frontend failed, after parsing finished)` in batch 61. The batch-70/73 frontend
fixes make these tasks parse for the first time, and they then hit the **pre-existing false
`valid-deref` on the alloca/malloc string family** — the very same "F1 flood" recorded as the
blocker for the flat memory model (81 false-derefs there). It is visible under the *default* model
now only because the tasks finally get far enough to be judged.

**This is the highest-value open item.** A wrong `false` scores −16; the same task answered
correctly scores +2. Fixing the 30 `cstr*`/`openbsd*` false-derefs is worth roughly **+540 score**,
far more than the entire +155 this run gained. Two termination LDV tasks are also wrong
(`false(termination)`, expected true) — those reproduce locally on batch 61's build too, so they are
pre-existing and were merely masked by OOM.

## Batch 76 — five of the seven run-79 frontend classes fixed; run 80 on benchcloud at 900s (2026-07-28)

Worked the run-75 frontend breakdown in the agreed order. Landed (`7de55d4797`, `b05791081c`):

| # | class | runs | outcome |
|---|---|---|---|
| 1 | `AllocaFunctionPass` double-remove | 193 | **fixed**, 3/3 sampled parse |
| 2 | `typeof` over a variable | 155 | **fixed**, 3/3 sampled parse |
| 3 | missing semantic cast (`TypeUtils.cast`) | 164 | **fixed**, 3/3 sampled parse |
| 5 | pointer arithmetic / LHS | 251 | **fixed as a side effect of 3** — those expressions go through `castTo`; 0 pointer-arithmetic errors left in the sample |
| 7 | byte-union nested aggregate element | 903 | **fixed**, 8/10 sampled parse |
| 7b | address of multi-byte union member | 174 | **lifted under the bytes model only** |

⚠️ **Item 4 (function pre-registration, 918) was implemented and then REVERTED.** Extending the
batch-70 pre-registration loop to function *declarations* did resolve the ordering case (`memcpy`
used at line 6372, declared at 6507), but `declarationVisitor.getDeclarations` has side effects and
calling it early broke three known-good LDV canaries (`ez_devices` stopped resolving) — 255 parse
canaries fell to 252. Measured gain on 20 sampled tasks of the class: **0** now parse, because each
merely advances to the next unresolved symbol. Negative net value, so it is out. The residual is
heterogeneous — kernel externs of opaque type (`__this_module`, `platform_bus_type`), static
functions referenced from struct initialisers (`uvc_probe`), locals. Every isolated reproduction of
the suspected declarator forms **parses fine**, so the cause is context-dependent and still open.

⚠️ **Item 6 (pthread candidate sets, 415) NOT implemented.** Enumerating candidates needs the array
extent, and the way the code gets that today is by unrolling the loop — which is exactly what fails
here (goblint's `pthread_t t[10000]` is 10x over `UNROLL_LIMIT`). Worse, dispatching `pthread_create`
over N candidate handles multiplies *thread identity*, and the failure mode of getting it wrong is a
**silently hidden race**, which 30 race canaries cannot be relied on to catch. Wants its own
validation cycle. The 118 affected tasks are dominated by goblint `28-race*` (39) and `09-regions`
(13). Note the earlier claim that this class is mostly 10000-element arrays came from the batch-70
note, not from data; the family breakdown here is new.

Also left deliberately: the **floating-point union member** refusal (287) is the batch-59 NaN gate on
`fpToIEEEBV`, an unsound round-trip that must not be reopened as a side effect.

### Run 80 — benchcloud, 900s

First run on **benchcloud** rather than sosy, at the real SV-COMP time limit: `xmls/theta27-long900.xml`
(`timelimit="15 min" hardtimelimit="16 min"`, 7 GB, 2 cores), tool dir `Theta-svcomp-80`, pinned to
`--vcloudCPUModel Skylake`, `--vcloudClientHeap 8192`, screen session `theta-bench-80`.

benchcloud's vcloud is Intel Xeon (Skylake); sosy's was AMD Ryzen 7 PRO 5750G, and the limit moved
300s -> 900s. **Compare run 80 against run 79 anyway** — the delta is informative and these
differences are usually not large enough to swamp the signal; just read the resource-shaped
categories (timeout/OOM) with the confound in mind rather than treating them as pure regressions.

Two parts of the comparison are *confound-free* and should be read directly:

- **Frontend failures are deterministic** — they do not depend on CPU or time limit at all. The
  run-79 -> run-80 delta in the `ERROR (frontend failed …)` buckets is attributable to the batch-76
  fixes and nothing else. Expected to fall by roughly the classes above (193 + 155 + 164 + 251 +
  903 + 174, minus the layering effect that made batch 73's 108 fixes net only -20).
- **Wrong results** are likewise mostly determinism-driven, so a change there is a real signal
  (with the caveat that a longer limit lets some tasks reach a verdict they previously timed out
  before reaching, which can *expose* latent wrong answers — as run 79 did for the alloca-string
  family).

Correct-count and score deltas carry both the hardware and the budget change; expect the 900s limit
alone to convert a large share of run 79's ~18,000 timeouts.

⚠️ The abs-path trap fired on the first launch attempt: `~/Theta-svcomp-80` expands before `ssh`, and
benchcloud's `run-theta.sh` also uses `--hidden-dir /home --overlay-dir "$PWD"`, so the container
cannot resolve `theta-start.sh`. Killed and relaunched with the relative `Theta-svcomp-80`; health
check then showed 0 "Cannot start process" and submissions accumulating.

## Batch 77 — run 80 (benchcloud, 900s): the 300s limit was hiding a large unsoundness (2026-07-29)

Run 80 = batch-76 build, benchcloud, `theta27-long900.xml` (900s), Skylake-pinned. Real & complete:
55 XMLs, 0 `Cannot start process`, screen gone, 22:15 -> 19:45 (~21.5h).

| category | run 79 (sosy, 300s) | run 80 (benchcloud, 900s) | Δ |
|---|---|---|---|
| correct | 10,861 | 12,521 | **+1,660** |
| wrong | 83 | **399** | **+316** |
| error | 25,308 | 22,932 | −2,376 |
| unknown | 350 | 750 | +400 |
| **score** | **16,475** | **13,734** | **−2,741** |

**+1,660 correct and the score still fell by 2,741**, because 316 new wrong answers at −16 each swamp
the gains. Transitions: `error->correct` 1,818, `error->wrong` **316**, `correct->error` 156.

### The confound-free part: the batch-76 frontend fixes worked

Frontend failures are deterministic, so this delta is attributable to the fixes alone:
**4,702 -> 3,955 (−747)**. Nominal target was ~1,840; the shortfall is the usual layering (a task
clears one barrier and stops at the next), and this is a far better conversion ratio than batch 73's
108 fixes for a net −20.

### ⚠️ The headline: 278 of the 316 new wrong are ONE family

`unreach-call.Hardness`, and within it **every one is `hardness_wrappers_*`, all reporting
`false(unreach-call)` where the expected verdict is `true`** — 278 spurious counterexamples.
All of them **TIMED OUT at 300s**. The Hardness set as a whole: run 79 had 1,060 correct / 2 wrong;
run 80 has 1,035 correct / **280 wrong**.

So this is not a regression from the batch-76 work. It is a **pre-existing unsoundness that the 300s
limit was masking**: given enough time the analysis runs to completion on these tasks and produces a
wrong counterexample. Since SV-COMP runs at 900s, **this is the real behaviour**, and every short-
benchmark score to date has been flattered by it. 278 wrong is ~4,450 score points — fixing this one
family more than recovers the entire −2,741.

Overall direction of the new wrong: **304 false alarms / 12 missed bugs**; 305 of 316 were TIMEOUT in
run 79, 11 were frontend errors.

Those 11 are worth naming: `softsign_*` / `tanh_*` `.c-amalgamation` NN tasks that the batch-76
**alloca double-remove fix** unblocked, which now return `false(unreach-call)` — the same
expose-a-latent-bug pattern as the alloca-string family in run 79. Unblocking the frontend keeps
converting errors into wrong answers rather than into correct ones, which is the third independent
sighting of that effect.

### Resource shift (carries the hardware + budget confound)

timeout 18,049 -> 12,407 (−5,642) but OOM 2,503 -> **6,499** (+3,996): a longer budget lets a run
allocate its way into the 7 GB cap instead of being cut off first.

### Priority

1. **`hardness_wrappers_*` false `false(unreach-call)`** — 278 tasks, one family, ~+4,450 score.
2. The alloca-string / newly-parsing false-deref family (still open from batch 75).
3. Everything else.

## Batch 78 — the hardness unsoundness root-caused and fixed; remaining wrong triaged (2026-07-29)

### Root cause: a global pointer split in one procedure, left unsplit in every other

All 278 `hardness_wrappers_*` false `false(unreach-call)` results come from one bug in
`ReferenceElimination` under `--memory-model multi`.

The pass decides **per procedure**. `runComplexReferenceElimination` returns early unless the
procedure itself contains a `ref(deref(...))`, and case 1 returns even earlier unless it contains a
reference or a *directly* referenced global — `getDirectReferencedDecl` only matches `ref(x)`, never
`ref(deref(q,i))`. So for

```c
long q[3]; long *p;
long readp(void) { return *p; }     // no reference of its own -> skipped entirely
int main(void) { p = &q[1]; ... }   // splits p into p_base / p_offset
```

`main` rewrites its accesses onto the halves while `readp` keeps dereferencing the original `p`,
**which nothing assigns any more**. `p` is unconstrained, so the solver may alias it freely; in the
hardness wrappers it picks `SL2 == SL1`, so `*SL2 = *SL1 + *SL0` clobbers `*SL1` and the property
genuinely fails *in the model*. Every conjunct of those tasks fails for the same reason, which is why
the family looked like a property bug rather than a memory-model one.

**Confirmed spurious by execution**: compiled natively with theta's own witness values
(`A[0] = -1040187392`, `A[1] = 0`), the property holds and no error is reached.

Fix: the split of a **global** is now computed once for the whole XCFA and cached on the parent, so
every procedure rewrites those globals onto the same halves, and both early returns stand down when a
procedure merely *uses* such a global. Flat/bytes never split, so they are untouched.

Minimal repros (all Unsafe before, Safe after): deref in a callee at offset 1 (`p1`) and at offset 0
(`p5`), write through a callee (`p2`), and the reduced wrapper (`r1`). Deref in `main` (`p4`) was
always Safe — the fold hides the bug whenever the reference and the dereference sit in one procedure,
which is why it survived so long.

⚠️ On the real tasks this converts **wrong -> no verdict**, not yet wrong -> correct: locally the two
sampled wrappers reach no verdict in 500s. That is still +16 score each. Run 81 (Hardness only, 900s,
benchcloud, Skylake) will show how many become `correct`.

### Canary set extended (260 tasks)

Five shapes this work unblocked, so they cannot silently regress: a global element pointer
dereferenced in a callee, `alloca` in the init procedure, `typeof` over a real variable, a byte-union
aggregate array element, and a semantic cast before a bitvector conversion.

### The other 119 wrong results are NOT the same bug

Re-checked a 12-task sample on the fixed build: 2 improved to no-verdict, **10 still wrong**. So the
remaining families each need their own root cause:

| family | n | direction |
|---|---|---|
| `cstr*`/`openbsd*` alloca-string | 32 | false `valid-deref` |
| `aws_*` harnesses | 11 | mixed |
| `scopes*` / `test-*` / `nested_structure_noptr` | ~20 | both directions |
| concurrency misc (`bounded_mpmc`, `mcslock`, `ticketlock`, …) | ~10 | false `valid-deref` |
| `memleaks_*` | 6 | |
| `softsign_*`/`tanh_*` NN | 7 | false `unreach-call` |

⚠️ The `softsign_*`/`tanh_*` tasks are ones the batch-76 **alloca fix unblocked**, and they now land
on a *different* false alarm. Same pattern as the alloca-string family: unblocking the frontend keeps
converting errors into wrong answers. That is now the fourth sighting, and it is the strongest
argument yet for fixing the `valid-deref` over-approximation before any further frontend work.

By property the remainder is dominated by **valid-memsafety (68 of 119)**, and by direction it is
84 false alarms / 35 missed bugs.

## Batch 79 — valid-deref false alarm narrowed to "pointer parameter incremented in a loop inside a callee" (2026-07-30, IN PROGRESS)

The `cstr*`/`openbsd*` alloca-string family (32 wrong, `false(valid-deref)` against expected `true`).
Representative task, `cstrchr-alloca-1`, is 12 lines of actual code:

```c
char *cstrchr(const char *s, int c) { while (*s != '\0' && *s != (char)c) s++; return ...; }
int main() {
  int length = __VERIFIER_nondet_int(); if (length < 1) length = 1;
  char* s = (char*) __builtin_alloca (length * sizeof(char));
  s[length-1] = '\0';                 /* terminator stops the scan -> safe */
  cstrchr(s, __VERIFIER_nondet_int());
}
```

Minimal repro reproduces the false alarm (`scratchpad/deref/scan.c`). The trigger has been narrowed by
elimination — each of these was run and is recorded, not assumed:

| variant | verdict | conclusion |
|---|---|---|
| `s[length-1]=0; assert(s[length-1]==0)` (symbolic size **and** offset) | **Safe** | the symbolic-offset write IS visible — hypothesis killed |
| `alloca(2147483647)` / `1073741823` / `100`, deref offset 0 | **Safe** | large/symbolic size alone is fine — hypothesis killed |
| scan **inlined into main**, symbolic length ≤ 6 | **Safe** | not the loop as such |
| `p=p+1` then deref, in main | **Safe** | not pointer increment as such |
| loop `p++` then deref, in main | **Safe** | not loop-increment as such |
| single increment inside a **callee**, all concrete | **Safe** | not the call boundary as such |
| terminator at concrete offset 0 (loop exits immediately) | **Safe** | the loop must actually iterate |
| **scan in a callee, `length` bounded ≤ 6** | **Unsafe** | reproduces |
| **scan in a callee, `length` fully concrete (6)** | **Unsafe** | reproduces |

So the trigger is specifically **a pointer parameter incremented inside a loop in a callee**, and it
reproduces with a *fully concrete, bounded* program — which makes it a **modelling bug, not an
abstraction imprecision**. (A bounded 6-byte program is finite and trivially provable.)

The `valid-deref` check itself (MemsafetyPass.kt ~line 200) is
`base <= 0 || size[base] <= offset || offset < 0`, with the size looked up **keyed by the base**. The
suspicion is therefore that in this shape the deref's base is not the value the allocation recorded a
size under, so `size[base]` is unconstrained and the middle disjunct becomes satisfiable. Note
`ReferenceElimination.seedSplitParams` already exists to fix an earlier instance of exactly this
symptom ("a false `valid-deref` on every `str*`-style callee that increments its argument"), so this is
a *remaining* hole in that mechanism, not virgin territory.

⚠️ NOT yet confirmed: which base the deref actually carries. The confirming step is to dump the model
— but `--enable-c-serialization` writes nothing under the memsafety property (it works under
unreach-call), so the next step is `--enable-xcfa-serialization`, or an observational test
(a callee that loop-increments then writes, checked from the caller). Do not write the fix before that
is nailed down; two hypotheses have already been killed by measurement here.

## Batch 80 — run 81 confirms the hardness fix (280 wrong -> 0); five families root-caused (2026-07-30)

### Run 81: the ReferenceElimination cross-procedure split fix is confirmed on the real benchmark

Hardness-only, 900s, benchcloud/Skylake, 6,789 tasks — same set as run 80, so directly comparable:

| category | run 80 (before) | run 81 (after) |
|---|---|---|
| **wrong** | **280** | **0** |
| correct | 1,035 | 1,050 |
| error | 5,474 | 5,739 |

Transitions: `wrong->error(TIMEOUT)` **274**, `wrong->correct` **6**, `error->correct` 26,
`correct->error(TIMEOUT)` 17. **NEW wrong: 0.** So every one of the 280 false alarms is gone and
nothing regressed into a wrong answer. At SV-COMP weights that is roughly **+4,500** on this family
(280 x 16 recovered, minus ~34 for the 17 that slipped to timeout).

⚠️ Most became TIMEOUT, not `correct` — the fix removes the spurious counterexample but the tasks are
then genuinely hard, so the gain is "no longer penalised", not "+2 each". Do not double-count it.
(`compare_runs.py` cannot score run 81 against run 80: the Hardness-only xml has one rundefinition and
the task keys do not align — `common: 0`. The per-task transition table above is the valid comparison.)

### Five families root-caused by parallel investigations

Full write-ups preserved in `benchmark-results/findings-run80/` (1,761 lines). Headline: **several
families share ONE cause**, and it is not what any of the per-family hypotheses assumed.

**SHARED ROOT CAUSE — the valid-deref check is not flat-model-aware.** `MemsafetyPass.annotateDeref`
(MemsafetyPass.kt:201-220) builds
`Or(Leq(deref.array, 0), Leq(sizeVar[deref.array], deref.offset), Lt(deref.offset, 0))`, assuming
`deref.array` is an object **base id** and `sizeVar[base]` its whole size. Under
`--memory-model flat`, `ReferenceElimination.runFlatReferenceElimination` collapses `&(deref B O)` to
the single scalar `B + O`, so a **mid-object address** legitimately lands in the `array` slot. The size
array has an entry only at `B`, so `sizeVar[B+O]` reads 0 and the middle disjunct is a **tautology** —
the edge to `__THETA_bad_deref` is enabled on every path. Guaranteed false `false(valid-deref)`.

Five-line repro, sequential, no threads, no heap:
```c
struct S { int a; int b; };
struct S s;
int main(void) { int *p = &s.b; return *p; }     /* flat: Unsafe. expected Safe */
```
Trigger is *any* deref through `base + nonzero offset`; offset 0 works because `base+0 == base`.
Confirmed on ticketlock by dump: `(<= (read __theta_ptr_size 131073) 0)` where 131073 = `lock*`(131072)+1
and only 131072 ever gets a size.

**Why concurrency tasks are affected at all: they are not really concurrency bugs.** The `multi`
frontend throws `UnsupportedPointerSplitException` on `&l->owner`-style mid-object arguments and the CLI
**silently falls back to flat**, where the instrumentation is broken. Ruled out by the investigator:
interleaving/OC (a 5-line single-threaded file reproduces it; OC dies with code 201 and never produces
these verdicts) and abstraction imprecision (the bad-deref assume is unconditionally true, so the cex is
feasible *in the model* — refinement cannot help).

⚠️ **A second flat defect constrains the fix.** Flat object bases are minted inconsistently: globals and
alloca objects get `flatBaseValue(id) = id * 65536`, but address-taken **locals** use `__sp`, whose init
is `cnt` and whose increment is `+3` — **unscaled** (ReferenceElimination.kt:252 and :269). So the
obvious base recovery `(addr / 65536) * 65536` would map every `__sp` object to base 0 (NULL) and trade
one false alarm for another. **Any fix must scale `__sp` too** (init `flatBaseValue(cnt)`, increment
`3 * FLAT_STRIDE`). That scaling is independently valuable: today local objects sit 3 apart inside the
first stride slice while `allocateReferenced` may give them a size > 3, so two distinct locals **overlap
on the flat address line** — a latent aliasing unsoundness, and the most likely mechanism behind
`bounded_mpmc_check_full`'s false `false(no-data-race)` (not verified).

**Other confirmed causes** (details in findings-run80/):
- *NN amalgamation (7)*: a **local** aggregate with a partial brace initializer is not zero-filled —
  `float a[4] = {0}` writes only cell 0, cells 1..3 stay unconstrained, violating C11 6.7.9p21. Globals
  do this correctly; `FunctionVisitor.flattenInitializer` never pads. Independently reproduced here:
  `LOCAL float a[4]={0.0f}` and `LOCAL int a[4]={1}` are both **Unsafe**. Blast radius: 656 files under
  `c/` contain `[N>=2] = {0}`. NOT an "uninitialized memory" bug — zero-fill is *required* by C for
  declarations that have an initializer, and the no-initializer nondeterministic path is correct and
  must not be touched.
- *filter2_alt*: the `static` storage class is **silently dropped** (`TypeVisitor.java:381`
  `case "static": return null;`), so a static local is re-`alloca`d per call and never persists.
- *scopes/test-\**: five distinct causes (A-E), including a nested struct initializer flattened onto the
  outer object, `(*p).field` taking one dereference too many, storing a split pointer writing both halves
  to the same cell, and a local array of structs allocated `dim` cells instead of `dim * cellsPerElement`.
- *aws_\**: two confirmed bugs (A is `multi`-only), 3 false alarms + 8 missed bugs.
- *no-overflow*: `Stockholm-2`/`dijkstra6` are additive-chain instrumentation gaps; `test22-2` is
  `ReferenceElimination` **silently deleting all overflow instrumentation** from a procedure.

### Sequencing

1. **Flat valid-deref base recovery + `__sp` scaling** — one fix, unblocks the largest set (the whole
   concurrency valid-deref subgroup, `stpcpy`, scopes cause B2, and probably the alloca-string family
   that motivated this batch, since those fall back to flat too). Must be done as one change.
2. **Local partial-initializer zero-fill** — 7 NN wrongs, precedented by the global path, but measure
   model blow-up (a local is emitted per inlined call site).
3. scopes causes A/C/D/E, aws A/B, overflow families — smaller and independent.
4. `static` storage duration — larger, worth 1 task here.

### Batch 80 addendum — flat valid-deref fix landed; two bugs uncovered on the way (2026-07-30)

Landed as `145bffaac0`. Verified by the investigator against the rebuilt jar, not just by me: the
5-line repro, `arr.c` and `midfield.c` are all Safe now (were Unsafe), and the real ticketlock guard
became `size[(div 131073 65536)*65536] <= (131073-base)+0` → `2 <= 1` → false.

Two bugs the fix uncovered, both now fixed in the same commit:

- **`MemoryFunctionsPass.fill` built the filler in the argument's type**, then cast it to the element
  type: `memset(p, ' ', n)` produced a `Bv32` cast to `Bv8` → ClassCastException → whole frontend
  failed. C converts the argument to `unsigned char`, so it is converted to the element type now.
  **Caught by the `discover_list` canary added the day before** — the canary set paid for itself
  within a day, one commit after the byte-union work that introduced it.
- **"Pointer arithmetic not supported" now throws `UnsupportedPointerSplitException`.** It is a
  multi-only representational limitation, so the CLI can silently rebuild under flat (which handles
  any pointer-arithmetic shape) instead of failing the task. ⚠️ This also **corrects batch 76**: the
  pointer-arithmetic class was *not* fully resolved by the semantic-cast fix. It was merely absent
  from the 5-task sample I checked; `uthash_JEN_test5-1` still hit it.
- `Mod` -> `Rem` in `annotateFree`: pointer types are unsigned bitvectors and Theta's `Mod` is
  signed-only. Latent until flat started being reached for these tasks.

⚠️ **Recorded narrowing of the flat fix.** Recovering the base by truncation means an access more
than `FLAT_STRIDE` (65536) cells past its base is now attributed to the *next* object's slice and
accepted, where it used to be caught accidentally by the missing-size tautology. Small exposure, but
a genuine loss of detection under flat — noted so it is not rediscovered as a mystery later.

Also from the investigator, and **worth doing next**: `div`/`mod` in the new guard are not
constant-folded, so the model literally carries `(div 131072 65536)` on every deref guard. Folding
literal div/mod in `SimplifyExprsPass` would recover most of that cost.

### Still open, with root causes in hand (see findings-run80/)

1. **Array object sized by element count, not flat cell count** (concurrency subgroup B). Any array
   whose element spans more than one flat cell, in any storage class. 2-line repro:
   `int arr[3][2]; int main(void){ arr[2][1]=1; return arr[2][1]; }` → Unsafe. Fix sites:
   `FrontendXcfaBuilder.kt` global path (~752-755) uses `getArraySize` where it needs
   `flatArraySize`; `giveStructObjectStorage` (~329) sizes structs as `unitCount` and never recurses
   into `CArray` fields. Risk assessed as **low — cannot hide a real invalid deref** (it only
   enlarges objects over cells that genuinely belong to them), and no race risk since MemsafetyPass
   is off for `no-data-race`. Unresolved: which frontend site mints the wrong size on the *local*
   path (`allocateStackArray` names `flatArraySize`, which would give the right answer, yet the model
   shows the element count).
2. **Local aggregates with a partial brace initializer are not zero-filled** (7 NN wrongs).
3. `static` storage class silently dropped (`filter2_alt`).
4. scopes causes A/C/D/E; aws Bug A + Bug C and the 8 negated harnesses; no-overflow additive chains;
   `test22-2`'s deleted overflow instrumentation; `memleaks_*`; `2SB`/`4SB`.

Corrections from the investigators worth keeping: **`stpcpy` is the flat subgroup, not the
str*-pointer-param bug** (it *cannot* run under multi at all — "bare use of split variable"), while
`rec_strcopy_malloc` does run under multi and is the str* one.

## Batch 81 — arrays sized by flat cells; the value bug that shipped with it (2026-07-30)

Landed as `03ebee79c8`. Root cause supplied by the concurrency investigation, which also found the
site I could not: `allocateStackArray` was a red herring (never called for a declared local array).

An array whose element spans more than one flat cell was registered with its **element count** while
every access indexes it in **cells** (`a[i].f` -> `a[i * unitCount + f]`). The recorded size was
therefore smaller than the object's addressable range, so `size <= offset` was satisfiable for good
accesses. Two-line repro, was Unsafe, now Safe:
`int arr[3][2]; int main(void){ arr[2][1]=1; return arr[2][1]; }`

Three sites fixed: `FunctionVisitor` (the `alloca` for a declared local array passed the bare outer
dimension — built as an *expression*, since a VLA dimension is a runtime value), and the global
`allocate` bound in `FrontendXcfaBuilder` both with and without an initializer.

**A wrong-*value* bug shipped with it, deliberately, because size alone was not enough.** An
uninitialised global aggregate array fell through to the per-element path, which gives every element
its own base id and zeroes *those objects* rather than the flat cells accesses read. `arr[0].a` came
back holding element 0's **base id as integer data**, and cells 3..5 were never written. That is a
value-level unsoundness independent of memsafety — it produced a wrong `unreach-call` verdict.
Now the flat cells are zeroed directly (C zero-initializes a global without an initializer).

### Corrections from the investigation — worth keeping

- ⚠️ **Subgroup B blocked 4 of the 5 flat concurrency tasks, not one.** Registered vs needed:
  `mcslock` 3/6, `elimination_backoff_stack` 4/12, `safestack_relacy` 3/6, `cnalock`/`bounded_mpmc`
  same shape. Only `ticketlock` was cleared by the earlier flat fix (`145bffaac0`) — it has no
  multi-cell array.
- ⚠️ **`bounded_mpmc_check_full`'s false `false(no-data-race)` is NOT fixed by the `__sp` scaling.**
  Both candidate mechanisms were disproved: its `q->buf[...]` slots are plain `void *`, not atomic,
  so there is no atomicity exemption to miss, and the dump shows every base a clean stride multiple
  so there is no aliasing. It is the **CAS/ownership-gated CEGAR precision gap** already recorded in
  memory for libvsync. Do not count it as fixed.
- The `--portfolio STABLE` sweeps run outside the shared lock starved seven queued jobs; several
  "timeouts" in the investigation logs are queue starvation, not results, and are labelled as such.

Canaries added for both shapes (`mcslock`, `safestack_relacy`), bringing the set to 262.

### Remaining, in order
1. Local aggregates with a partial brace initializer are not zero-filled (7 NN wrongs) — same family
   of bug as the one just fixed, but on the *local* path and *with* an initializer.
2. `static` storage class silently dropped (`filter2_alt`).
3. scopes causes A/C/D/E; aws Bug A/B/C + 8 negated harnesses; no-overflow additive chains;
   `test22-2`'s deleted overflow instrumentation; `memleaks_*`; `2SB`/`4SB`.
4. Fold literal `div`/`mod` in `SimplifyExprsPass` to recover the per-deref guard cost.

---

## Batch 82 — seven wrong-value bugs, all in how a variable gets the value it starts with

Worked directly (no investigators) from the banked write-ups in `findings-run80/`. Four commits on
`svcomp27-fixes`: `dea85df263`, `2ff05ca895`, `8e08530615`.

Every one of these is a *wrong-`false`* class defect: the model let the solver read something the C
program never put there. None of them needs a pointer or a memory-safety property to bite.

| # | Bug | Was |
|---|-----|-----|
| 1 | local aggregate with a partial brace initializer not zero-filled | `float w[N]={0}` arbitrary from cell 1 on — every NN weight table |
| 2 | `char s[N] = "lit"` wrote **nothing**; emitted `s = 1`, clobbering the array's base | local, an unrelated global with an equal literal, and the bare literal all collapsed onto object id 1 |
| 3 | `alloca` bases collided with compile-time global bases | 2 globals + 1 local array was enough: initialising the local overwrote the global |
| 4 | character constants decoded by hand | `'\x41'` read as octal, `'\101'` as decimal, `'A'` as 97 (text lowercased), and `'\n'` threw NumberFormatException *out of the frontend* |
| 5 | `static` storage class returned `null` from the type visitor | every static local re-initialised on entry (`filter2_alt`'s filter state, one-shot guards, counters) |
| 6 | local aggregate initializer wrote flat cell offsets (scopes cause **A**) | `struct Outer o={{1,2},3}` destroyed the nested object's base and collided the last two writes on one cell |
| 7 | `(*p).f` double-dereferenced (scopes cause **C**) | `ldv-regression/test22-1`, expected `true`, was a wrong `false`; now Safe |

**#3 is the one worth remembering.** Pointer bases are partitioned by residue mod 3 — `3k+0` heap,
`3k+1` stack, `3k+2` address-taken — and `alloca` shares the `3k+1` class with the frontend's
*compile-time* bases (`ptrCnt`, also `3k+1`). The runtime counter started at zero, so the first
stack object took base 4, which the second compile-time object already owned. The frontend now
publishes its high-water mark on `XcfaBuilder.metaData` and `MallocFunctionPass.ensureMallocVar`
seeds the counter at or above it, still on a multiple of three so the residue classes keep meaning
what they mean. **`ReferenceElimination` has the same shape of hazard and was NOT audited**: its
`__sp` starts at a compile-time id from the *same* `cnt` counter it later hands out ids from, so a
runtime `__sp` step can land on an id given to a different address-taken object. Worth a repro.

**The canary harness grew verdict fixtures.** All seven bugs parse perfectly — a miswritten memory
cell is not a parse error — so `run_fixtures.sh` now accepts `SAFE`/`UNSAFE` as an `expect` value
and runs the real portfolio for those rows. Eight new fixtures (32 total); keep them small, they
run on every gate.

Gate for all four commits: 262/262 parse, 32/32 fixtures, the array/string verdict subset 29/30
(1 timeout), guard set unchanged (its only failures are its own `kind=wrong` rows; every `neighbor`
passes), c2xcfa/xcfa/c-frontend unit tests green.

### Remaining, in order
1. scopes cause **F** — `memcpy`/`memset` convert bytes to cells with a fixed 4-byte divisor.
   ⚠️ `memset(p, 0, sizeof *p)` on an aggregate is everywhere in the benchmark set; fixing it moves
   many verdicts at once, so it wants **its own benchmark run**, not a ride-along.
2. scopes cause **D**/B1 — storing a base/offset-split pointer writes both halves to the same cell.
   Needs a design decision, not a patch; findings recommend throwing `UnsupportedPointerSplitException`
   so the CLI rebuilds under `--memory-model flat`, which represents a mid-object pointer natively.
   Wide blast radius — price it with a full run.
3. scopes causes **G**/**H**/**I**/**J** — objects never die (block scope, `alloca` at return), freed
   addresses never reused, no VLA length check. These are the 7 *missed bugs* in the family.
4. aws Bugs A/B/C + the 8 negated harnesses (`findings-run80/aws.md`).
5. no-overflow: additive chains (`Stockholm-2`, `dijkstra6-both-nt`), and `test22-2` where
   `ReferenceElimination` silently deletes ALL overflow instrumentation from a procedure.
6. `memleaks_*`, `dirname-1`, `2SB`/`4SB`. `dirname-1` needs the *bare* string literal to become a
   real object with its bytes — item 2 above only covers the `char a[N] = "lit"` declaration form.
7. Cleanups: drop `allocateArrayElements`' now-redundant per-element subobjects (`outerarr`
   slowness); fold literal div/mod in `SimplifyExprsPass` to shrink the per-deref guard.

### Run 82 launched 2026-08-03 22:04 (benchcloud)

`Theta-svcomp-82` = `d8f0a698c2`, `xmls/theta27-long900.xml` (900 s), `--vcloudCPUModel Skylake
--vcloudClientHeap 8192`, screen session `theta-bench-82`, log
`~/bench-theta27-82-20260803-2204.log`, results under
`~/results/Theta-svcomp-82/theta27-long900.xml/2026-08-03_22:04:16/`.

**Baseline for the diff is run 80** — same XML, same host, same CPU model
(`~/results/Theta-svcomp-80/theta27-long900.xml/2026-07-28_22:15:48/`). Run 81 is *not* comparable:
it used `theta27-hardness900.xml`.

Sanity checks before trusting progress: `grep -c "Cannot start process"` must be 0; `writeRunResult`
counts submissions, not completions; done = all `.xml.bz2` present **and** the screen session gone.

---

## Batch 83

### scopes cause F — `memcpy`/`memset` copied `n / 4` cells (`4521d52f7e`)

`MemoryFunctionsPass` turned a byte count into a cell count by dividing by an element width, and the
guard that was supposed to refuse a struct pointee never fired: **`CStruct`, `CArray` and `CPointer`
all extend `CInteger`**, so `embedded is CInteger` is true for a struct. `memcpy(p, &d, 4)` on a
four-`unsigned char` struct resolved its element to the *struct* (`width()` 32) and copied one cell,
leaving three of four holding whatever they held before — silently. A struct pointee now takes a
whole-object copy driven by the **cell layout** (a cell is one member, whatever its C width),
restricted to objects whose every cell is a scalar and to a byte count equal to the object's size.
`memset` likewise, zero fill only. Findings' repro: `(Property valid-free) Unsafe` → Safe.

⚠️ This moves many verdicts at once and wants its own run — do not read a mixed run as a measurement
of it.

### Item 7 (`ReferenceElimination.__sp`) — CLEARED, no bug. Do not re-investigate.

I flagged this in batch 82 as possibly the same shape as the alloca/static base collision. It is
not, and the reason is worth recording so nobody spends the time again.

`cnt` (companion object, `3k+2`) has exactly two consumers: the compile-time bases for address-taken
**globals** (`globalReferredVars`, :172) and the one-off seed of `__sp` (:259), which then steps at
*runtime* for address-taken **locals**. `globalReferredVars` is `computeIfAbsent("references")` over
*all* procedures and is called at `run()`:116 for **every** procedure — so every compile-time id is
handed out in one shot on the first procedure, before any `__sp` seed, and nothing reads `cnt`
afterwards. `__sp` therefore always starts above every compile-time id.

Measured (`scratchpad/w/sp2.c`: three address-taken globals + one split + three address-taken
locals): globals get **2, 5, 8**; `__sp` is seeded at **11** and steps 14, 17, 20. No overlap.

Residual, unrelated and low priority: `cnt` is static for the JVM's lifetime, so repeated in-process
XCFA rebuilds keep climbing. Harmless today (the portfolio forks a subprocess per configuration),
but under flat addressing ids are `× 65536` and a 32-bit pointer only has 65536 slices.

### Run 82 is STALLED in the vcloud queue — not a theta problem

As of 02:26 (4 h 22 min after launch): submission accepted ("Waiting for 36602 run results"),
client alive, connection ESTABLISHED, `Cannot start process` = 0, and **0 of 36602 results**.
Run 80 — identical flags, same host, `--vcloudPriority LOW`, `--vcloudCPUModel Skylake` — wrote its
first result **40 seconds** after that same line. So this is the cluster, not the launch: either the
Skylake pool is busy/unavailable or a LOW-priority job is sitting behind others. Not acted on: the
CPU pin is unconditional (see memory) and raising priority on a shared cluster is not ours to do.

### Cause J (zero-length VLA) — SHIPPED in `323c583fc7`. The note below is the failed first attempt.

**Ground truth confirmed** (the investigator's own confidence was only medium, so I checked): all
seven `loops/` tasks — `sum_array-1`, `sum_array-2`, `matrix-2`, `insertion_sort-1`,
`insertion_sort-2`, `invert_string-2`, `bubble_sort-1` — carry
`expected_verdict: false` **and** `subproperty: valid-deref`, and each sizes a VLA from an
unconstrained nondet with no positivity assume. C11 6.7.6.2p5 makes `n == 0` undefined, and the
model cannot see it: the object simply gets size 0, every `for (i=0;i<n;i++)` runs zero times, so no
dereference happens and no access guard can fire.

**The obvious placement does not work.** I emitted the `size <= 0` edge to `errorLoc` from
`AllocaFunctionPass` (pass group 2), guarded on `MemsafetyPass.enabled` and on the size not being a
literal. It compiles, it is emitted — and it is silently **neutralised**:
`MemsafetyPass.breakUpErrors` (pass group 12) begins by redirecting *every* incoming edge of
`errorLoc` to `finalLoc`, which is how `reach_error()` is disabled under memsafety. Measured:
`int A[M];` with unconstrained `M` still came back **Safe**. Reverted rather than left as dead code.

Nor can the check be parked on a location of its own for MemsafetyPass to wire up later —
`RemoveDeadEnds` (group 8) runs in between and deletes a location with no outgoing edge.

**So the check has to be emitted from inside `MemsafetyPass`, after `breakUpErrors`** — i.e. a new
`annotateEmptyAlloca` alongside `annotateDeref`. The hard part is telling an `alloca`-recorded size
from a `malloc`-recorded one there, because the invoke is long gone by then and **`malloc(0)` is
perfectly legal C** — it must not be flagged. Candidate discriminators, in order of robustness:
the base's residue class (`3k+1` stack vs `3k+0` heap, which `annotateFree` already tests with
`Rem(argument, 3)`); the `__malloc + 1` fingerprint that `StackArrayAllocaTest` keys on (may not
survive LBE/simplify); or a list of size expressions recorded by `AllocaFunctionPass` on
`builder.metaData` and matched *structurally* (not by identity — see the `cType` trap in
`4521d52f7e`'s sibling commit).

Also worth knowing before starting: `invert_string-2` additionally does `str1[MAX-1]` → `str1[-1]`
when `MAX == 0`, so it has a second, independent violation the existing negative-index guard should
already catch once the object exists.

**Second attempt, shipped.** The way past the `breakUpErrors` problem is not to emit an error edge
at all: `AllocaFunctionPass` now appends a **read of cell 0** to a runtime-sized stack allocation,
and `MemsafetyPass.annotateDeref` turns it into exactly the right check by itself — its guard is
`ptr_size[base] <= index`, which at index 0 *is* `size <= 0`. Smaller than the plumbing it replaces,
and immune to pass ordering because it is an ordinary dereference.

Confined to non-literal sizes (so `int a[10]` and the constant-sized subobject allocations cost
nothing) and to memsafety only (so `no-data-race` never sees a read the program did not perform).

**All seven `loops/` tasks recovered** — `sum_array-1`/`-2`, `matrix-2`, `insertion_sort-1`/`-2`,
`invert_string-2`, `bubble_sort-1` now report the expected `false`.

The exposure worth measuring was that the probe also covers explicit `alloca(n)`, and 45 of the
`array-memsafety/*-alloca-*` tasks expect `true`. Measured over all 52 tasks of both families:
one FAIL (`openbsd_cmemrchr-alloca-2`) and 44 timeouts at 90 s — **all pre-existing**, confirmed by
re-running them with the probe disabled, where they behave identically. `openbsd_cmemrchr-alloca-2`
clamps `n` to `[1, MAX]` before the `alloca`, so the probe cannot fire on it; it is an independent
wrong result and is *not* yet triaged. The 44 timeouts are that family's ordinary slowness (the
guard set has always had `cstrncpy-alloca-2` timing out).

### Run 84 launched 2026-08-04 09:40 (sosy) — benchcloud went offline

Run 82 on benchcloud never started (0 of 36602 results in 11.5 h; the host is down). Resubmitted on
sosy at **HEAD `323c583fc7`**, so run 84 measures batches 82 **and** 83 together — the isolation
that "cause F wants its own run" asked for is gone, and that is a deliberate trade: one measured run
beats none. Attribute F/J movement with care.

- tool dir `Theta-svcomp-84` (relative — an absolute path makes every run die as
  `Cannot start process` while looking like a completed benchmark)
- `xmls/theta27-long900.xml`, **created on sosy for this run** by taking `theta27-short.xml` and
  raising `timelimit` 5→15 min and `hardtimelimit` 6→16 min; identical in every other respect
  (verified by diff). sosy had no 900 s XML.
- `--vcloudCPUModel 5750G --vcloudClientHeap 8192`, tmux session `theta-bench-84`, log
  `/data/scratch/bajczi/bench-theta27-84-20260804-0940.log`, results under
  `results/Theta-svcomp-84/theta27-long900.xml/2026-08-04_09:40:17/`.

**Baseline is run 79** (`results/Theta-svcomp-79/theta27-short.xml/2026-07-28_13:13:07/`) — same
host, same XML content, same `5750G` pin, same client heap. The one difference is the time limit,
300 s vs 900 s, and it is asymmetric in a way that suits this batch: a longer limit can turn a
TIMEOUT into a result but can never turn a correct result into a wrong one. So **"correct in 79,
wrong in 84" is a real regression**; "newly solved in 84" is confounded by the extra time and must
not be counted as a win without checking the 79 status was TIMEOUT rather than a wrong verdict.

Benchcloud's run 82 was left queued rather than killed: if that host ever comes back it produces a
clean batch-82-only measurement, which is strictly useful.

### Backwards pointer steps lost their sign under integer arithmetic (`7cbb2fba3d`)

Started as item 3 (triage `openbsd_cmemrchr-alloca-2`, the wrong `false` found while measuring
cause J). It is not one task: **every backwards walk over a buffer was a false valid-deref alarm** —
the `cmemrchr`/`memrchr` idiom and any `while (n--) *--p;`.

A pointer step is counted in the pointer-sized *unsigned* type, so `p--` reaches
`ReferenceElimination` as `&*(p + 4294967295)` (ILP32). Under **bitvector** arithmetic that is
exactly `p - 1` — the addition wraps by construction. Under **integer** arithmetic nothing wraps, so
one `p--` left the address 2^32 too large and `ptr_size[base] <= offset` fired on the next read.
The tell: the sibling `n--` in the same loop was always correct, because the frontend wraps *its*
unsigned arithmetic. What was lost is the wrapping of the **reconstructed** address, in both places
the pass rebuilds one from `Reference(Dereference(base, off))` — the split path and the flat path.

**Re-sign the step literal (`+4294967295` → `+ -1`), do not wrap the sum.** Both are correct;
wrapping costs a `Mod` on *every* pointer step and was measured to turn a 3-second forward-scan
proof into a timeout. The literal has to be read through `ExprUtils.simplify` — it arrives inside
the frontend's casts, not as a bare `IntLitExpr` (matching on the bare literal silently does
nothing, which cost a build cycle to notice).

Bisection that got there, worth keeping: forward scan Safe / backwards Unsafe isolated it to the
*direction*, not to the one-past-the-end pointer or the function call; then a fully **concrete**
repro (`alloca(3)`, `cp = a+2`, walk down) still failing proved it was a modelling bug rather than a
precision one; then `--arithmetic bitvector` → Unknown vs `integer` → Unsafe pinned the arithmetic
mode. `openbsd_cmemrchr-alloca-2` itself is now a timeout rather than a wrong `false` (0 instead of
−16) and may resolve at 900 s.

### scopes cause D — storing a mid-object pointer is now refused (`25086001fe`)

A pointer value occupies one memory cell, so it must be stored as one value; a `(base, offset)` pair
is two. The pass emitted two `MemoryAssignStmt`s "one per channel" — but `multi` has one memory
array and one `__theta_ptr_size`, so for the common `struct { T *p; }` field both dereferences are
*identical* and the second store clobbered the first, leaving the cell holding the bare offset with
the base lost. Eight lines reproduce it (`struct C { int *p; } c; c.p = &a[1]; return *c.p;` →
`(Property valid-deref) Unsafe`); `test27-1` has the shape twice.

Took the findings' **option 1**: throw `UnsupportedPointerSplitException` so the CLI rebuilds under
`--memory-model flat`, where a mid-object pointer is a single scalar address. Flat is a better
destination than when the finding was written, because this batch fixed its pointer arithmetic
(`7cbb2fba3d`).

**The width was measured, not assumed.** A 62-task sweep of the two families most likely to switch
model (`ldv-regression` + `memsafety-ext3`, valid-memsafety), run with and without the change, is
**identical task for task**: 39 PASS / 12 TIMEOUT / 6 ERROR / 5 FAIL both ways. Keep that method for
model-level changes — the guard set alone (30 tasks) would not have caught a regression here.

Two things that sweep incidentally pinned down, both pre-existing and both still open:
- the 5 FAILs (`derefInLoop1`, `getNumbers1-1`, `scopes1`, `scopes3`, `scopes5`, all
  expected `false` / got `true`) are exactly the missed-bug set of causes **G/H/I** — item 2;
- the 6 ERRORs (`test24-1`, the four `test_union_cast*`, `naturalNumbers1`) are a **byte-addressed
  union with a floating-point member**, refused by the frontend
  (`ExpressionVisitor#unsupportedByteLaidOutMember`). Unrelated to pointers, not yet on the list.

`test27-1`/`test25-2` show no movement at 75 s — earlier fixes in this batch had already taken them
off their wrong `false` and onto timeouts.

### scopes cause H — stack objects now die at function return (`0ecbd6b1d6`)

`AllocaFunctionPass` has always *asserted* in its own doc that alloca memory "is released when the
function returns"; nothing ever emitted the release, so `__theta_ptr_size[base]` was written once at
the allocation and cleared only by an explicit `free`. **Any use-after-return of alloca memory was
accepted** — `memsafety-ext3/getNumbers1-1` (`return array;` then the caller reads through it) now
reports the expected `false`.

No new checking machinery was needed: `annotateDeref` already reports `ptr_size[base] <= index`, so
zeroing the size on the return edges makes the existing guard fire unchanged. Only the *last* base a
repeated allocation produced is released (a variable holds one value); releasing too few objects can
leave a bug unfound but never invent one.

Measured on the surface it most exposes — the 45 `array-memsafety/*-alloca-*` tasks all expect
`true`, so an early release would show as wrong `false`: **0 FAIL** over the 52-task alloca/VLA
sweep (45 TIMEOUT, 7 PASS).

### scopes cause G — still open. Read this before attempting it.

The remaining four missed bugs of the family: `scopes1`, `scopes3`, `scopes5`, `derefInLoop1`.
Same missing mechanism as H, one scope level down — an object's lifetime ends at **block** exit —
but it does *not* reduce to the same fix, for two reasons.

**1. It cannot be done in a pass.** Block-local allocas are hoisted out of their block (the findings
show `scopes5`'s array allocated in `main_init`), so by pass time there is no block boundary left to
attach a release to. It needs the frontend, where `FunctionVisitor` still has the structure — but
the scope stack is pushed/popped at **nine** sites (`visitBlockItemList`, `if`, `for`, `while`,
`dowhile`, `switch`, …), and each would need the release appended to *its* block's `CCompound`, plus
a marker invoke for a pass to turn into `deallocate`. That is a design addition, not a patch.

**2. `scopes1` is not an alloca at all.** Its `{ int myNumberA = 7; myPointerA = &myNumberA; }` is an
address-taken *scalar*, which `ReferenceElimination` gives a **compile-time** `3k+2` base allocated
once at procedure entry. Releasing it at block exit needs a separate mechanism from the alloca one.
So even a complete block-scope release for allocas gets 3 of the 4.

⚠️ **The cheap shortcut is unsound — do not take it.** "Release the old object when the same variable
is re-alloca'd" fixes `scopes3` and `derefInLoop1` for about five lines, and is wrong for explicit
`alloca()`: C keeps *that* memory alive until the **function** returns, not until the next iteration,
so a loop doing `p = alloca(n)` and keeping the old pointer would get a false `valid-deref` alarm —
a wrong `false`, the worst direction. Distinguishing declaration allocas from explicit ones by the
target variable's name is a naming heuristic and too fragile to rest a memory-safety verdict on.
(This is the same declaration-vs-explicit `alloca` distinction cause J ran into.)

### scopes cause G — block-scope lifetimes (`e56f8ab698`). 3 of 4; `scopes1` still open.

`FunctionVisitor` now keeps a stack of scope-bound objects in lockstep with its scope stack and
emits a `__theta_scope_end` marker at block exit; `AllocaFunctionPass` lowers it to the `deallocate`
that already existed. No new checking machinery — `derefInLoop1` proves the check was always right
(the model already gave each unrolled iteration its own base, it just never retired the old one).

Two things that were not obvious going in:
- **Loops need the release on the *body*, not the loop.** A loop's own scope spans the whole
  statement, so releasing there frees once instead of once per iteration. Taken from a high-water
  mark, so an object declared in a `for` init — which outlives the body — is not released with it.
- **Early exits are fine.** `break`/`goto`/`return` skip the release; releasing fewer objects can
  leave a bug unfound but never invent one, and `return` is covered by cause H.

**Property gating (user requirement: under anything but memory safety the XCFA must be unchanged).**
The c-frontend module cannot see `MemsafetyPass`, so the decision travels on a new
`ParseContext.checkMemsafety`, set in `ExecuteConfig` from the same `MEMSAFETY || MEMCLEANUP` test
that sets `MemsafetyPass.enabled`. With it false the frontend registers nothing and emits no marker,
so nothing needs stripping downstream. **Verified by diffing the serialised XCFA** for a program with
block-scoped arrays in a bare block, a `for` body, a `while` body and an `if` arm under
`unreach-call`, built both ways: byte-for-byte identical. Use that method for any future
memory-safety-only frontend work.

A/B over the 62-task `ldv-regression` + `memsafety-ext3` sweep: exactly three tasks move, all
FAIL → PASS (`derefInLoop1`, `scopes3`, `scopes5`); 11 TIMEOUT and 6 ERROR identical.

**`scopes1` needs a second mechanism** and is the last of the family: its
`{ int myNumberA = 7; myPointerA = &myNumberA; }` is an address-taken *scalar*, which
`ReferenceElimination` gives a compile-time `3k+2` base allocated once at procedure entry. There is
no `alloca` to scope, so the release has to come from wherever those bases are minted.

### ⚠️ Guard-set blind spot found: `scopes4-1`

It expects `true` and returns **Unsafe at 300 s** — a wrong `false` — but *times out* at the guard
set's 120 s, so the gate reports it as TIMEOUT and never as a failure. Confirmed pre-existing by
building without cause G and re-running (Unsafe either way); it is cause **B1**, a mid-object
pointer escaping into a scalar context. Two lessons: cause B1 is still live and unfixed, and a
guard-set TIMEOUT is not evidence of absence — check the slow rows with a longer budget before
trusting them.

### `T a[] = {…}` as a *local* crashes the frontend — fix written, NOT shipped, parked in a stash

`char numbers[] = {0,1,…,9};` takes its extent from the initializer, so the declarator carries no
dimension; `FunctionVisitor.visitBodyDeclaration` read it straight through into
`List.of(allocaSize)` and died with a bare **NullPointerException**. The *global* path has always
inferred the extent (`FrontendXcfaBuilder#getArraySize`); only the local one did not. A crude grep
finds the shape in **31** benchmark files across 8 families (eca-rers2018, ldv-linux-3.4-simple,
memsafety-cve, floats-esbmc-regression, sqlite, float-benchs, memsafety-ext3, libvsync).

The fix (infer the element count from the initializer, designators included, and let the existing
cell scaling convert it) is ~30 lines and works. **It is parked in `git stash` — do not ship it as
is.** Measured on those 31 files, before/after, with a build of each:

| | before | after |
|---|---|---|
| parse | 8 / 31 | 15 / 31 |

Seven newly parse — and **six of them time out** (`interpolation`, `interpolation2`, `nearbyint.i`,
`rint.i`, `zchunk.i`, `zchunkFixed.i`; still timing out at 320 s, not just 100 s). Crash → timeout
is 0 → 0. The only one that *resolves* is `memsafety-ext3/naturalNumbers1`, and it resolves
**wrongly**: `Safe` against an expected `false`, i.e. **−32**. So the whole measured effect of a
correct fix is −32.

Why `naturalNumbers1` is wrong is not the NPE's fault and cannot be fixed here: it declares
`char numbers[10]`, casts to `int *`, and reads `numbers[i]` — 40 bytes out of a 10-byte object. In
the **cell** model each cell is one element, so `ptr_size = 10` and reading cells 0..9 is in bounds.
Seeing that violation needs byte-granular memory. This is the same cell-vs-byte confusion recorded
as cause H's side finding (`alloca(40)` records 40 *cells*).

Two ways to unblock, for whoever picks this up:
1. Land the **bytes** memory model, after which this fix is straightforwardly positive — revisit then.
2. Refuse the shape instead of answering it: a cast from a `char` array to a *wider* pointer type is
   a reinterpretation the cell model cannot represent, so throwing `UnsupportedFrontendElementException`
   there would keep `naturalNumbers1` at 0 while the other six get their chance. Principled (it is the
   same discipline as the byte-union float refusal and `MemoryFunctionsPass#giveUp`) but unmeasured —
   it could turn currently-correct answers into 0, so price it before shipping.

**Erroring is worth 0; a wrong answer is worth −32. When the model is known to be unsound for a
shape, a loud failure is better than a confident answer** — that is why this is parked rather than
merged.

### C99 hex float constants were refused, killing the frontend on 134 files (`eab619083c`)

`0x1.4p+4` threw "Hexadecimal FP constants are not yet supported", which takes down the whole
frontend, not just the expression. **134 benchmark files contain one** — 104 in `coreutils-v8.31`,
the rest in `floats-cbmc-regression`, `ldv-regression`, `floats-esbmc-regression`.

A/B on the 30 non-coreutils files, built both ways: **0/30 parsed before, 16/30 after**. The other
14 fail for unrelated reasons. `ldv-regression/test_union_cast.i` and `test_union_cast-2.i` went
from crash to the expected `true`.

Java's literal syntax is C99's and `Double.parseDouble` reads it exactly — a hex literal names a
binary value directly, so nothing rounds. The fixture pins values, not just the parse. `long double`
keeps the refusal (wider significand than a `double`, so the round-trip could silently round).

### Item 3 was three unrelated causes, not one

The 6 "ERROR rc=210" tasks from the cause-D A/B split into:
1. `test_union_cast.i`, `test_union_cast-2.i` — **hex float constants**. Fixed above.
2. `naturalNumbers1` — **dimensionless local array** (`char a[] = {…}`) NPE. Fix written and
   **parked** — see the section above; it is net −32 until the cell/byte gap closes.
3. `test_union_cast-1.i`, `test_union_cast.c_1.i` — the genuine **byte-addressed union with a
   floating-point member** refusal (`ExpressionVisitor#unsupportedByteLaidOutMember`). Still open.
   Note what these tasks actually need: the `double` member is only ever *written*
   (`var.z = 0x1.4p+4; var.y = 10u; assert(var.y == 10u)`), never read. So a **constant** float
   store could write its exact IEEE-754 bytes at compile time — no `fpToIEEEBV`, no NaN round-trip,
   which is what the refusal exists to prevent. Reads stay refused. That looks like the cheap,
   sound way in; it was not attempted this firing.

---

## RUN 84 LANDED — first real measurement of batches 82/83

Finished 2026-08-05 18:47, all 36602 runs, 55 `.xml.bz2`, no `Cannot start process`, no OOM.
Results pulled to `benchmark-results/results-2026-08-04_09-40-run84/`; comparison script kept at
`scratchpad/cmp84.py` (reads both dirs, prints category totals, per-task moves and the SV-COMP score).

**Run 84 = `323c583fc7`** (batch 82 + causes F and J). Everything from `7cbb2fba3d` on — backwards
pointer steps, cause D, cause H, cause G, hex float constants — is **not** in it.

Baseline is run 79 (same host, same XML content, same `5750G` pin; 300 s vs 900 s).

| | run 79 | run 84 | delta |
|---|---|---|---|
| correct | 10860 | 12765 | **+1905** |
| error | 25239 | 22953 | **−2286** |
| unknown | 350 | 731 | +381 |
| wrong | 82 | 82 | **0** |
| **SV-COMP score** | **16490** | **19437** | **+2947** |
| correct true / false | 7310 / 3550 | 8320 / 4445 | +1010 / +895 |
| wrong true / false | 23 / 59 | 21 / 61 | −2 / +2 |

⚠️ **Do not read +2947 as the fixes' doing.** Run 84 had 3× the time budget, so most of the newly
correct results are the extra time. What the time limit *cannot* explain is the direction that
matters: **the wrong count did not move** (82 → 82) even with 3× the budget to reach more verdicts,
and wrong-*true* (the −32 class) went **down**. That is the real signal.

### The 3 genuine regressions (correct in 79 → wrong in 84)

More time cannot turn a correct answer wrong, so these are the model changing.

1. `termination-memory-alloca/openbsd_cstrncmp-alloca-1` [no-overflow] `true` → `false`.
   **Root-caused, see below.** Reproduces at HEAD.
2. `ldv-races/race-2_2-container_of` [valid-memsafety] `true` → `false(valid-deref)`
3. `ldv-races/race-3_2-container_of-global` [valid-memsafety] `true` → `false(valid-deref)`
   — both time out locally at 200 s, so not yet reproduced; they only answer at ~900 s.

27 more went from **non-answer to wrong**. Those are mostly 300 s timeouts that now get far enough
to be wrong — pre-existing wrongness becoming visible, not new. The exception worth noting: 8 entries
(4 `uthash-2.0.2` tasks × 2 properties) went from *frontend crash* to `false(valid-deref)`, i.e. a
batch-82 frontend fix unlocked them into a wrong answer — the same trap that got the
dimensionless-array fix parked.

## ROOT CAUSE: a narrow-typed memory cell is not range-constrained (integer arithmetic only)

Four probes, `--property no-overflow`:

| probe | verdict |
|---|---|
| `int r = a[0] - a[1]; return -r;` with `unsigned char *a = alloca(2)` **uninitialised** | **Unsafe** ← false alarm |
| same, but cells first written with `__VERIFIER_nondet_uchar()` | Safe |
| same arithmetic through plain `unsigned char` **variables** | Safe |
| the uninitialised version under `--arithmetic bitvector` | Safe |

So the gap is exactly: **an unwritten memory cell under integer arithmetic**. `HavocPromotionAndRange`
constrains *variables* to their C type's range; nothing constrains a *cell*, and under integer
arithmetic the array's default value is an unbounded Int. Under bitvector the cell's SMT type is
already narrow, and a written cell carries the cast its write applied — which is why only this one
combination misbehaves.

The difference of two `unsigned char`s is in [−255, 255], so `-r` cannot overflow *by typing alone*;
the reported trace is spurious. This is precisely the "belt-and-braces" note in
findings-run80/overflow_misc.md, and it explains **five** no-overflow false alarms at once:
the regression above, three of the 27 (`openbsd_cstrcmp-alloca-1`, `openbsd_cstrncmp-alloca-2`,
`openbsd_cstrcmp-alloca-2`), and `dirname-1` from work item 6.

**Suggested fix:** make a read of a narrow-typed cell yield the C type's range — i.e. wrap the
`Dereference` in `cType.castTo(...)` at the *read* site (never on an lvalue). Under integer
arithmetic that inserts the modulo/two's-complement wrap already used everywhere else, so the value
lands in [0,255] / [−128,127] by construction. Cost is a `Mod` per narrow memory read; gate it to
integer arithmetic, since bitvector needs nothing. Repros kept at `scratchpad/w/charcell*.c`.

### 🚫 sosy: no benchmarks until further notice (2026-08-06)

An admin asked the user to stop their processes on sosy. Checked at the time: **nothing of theirs was
running** — run 84 had already finished at 18:47 the previous day and its tmux session was gone; zero
java/python/vcloud/benchexec/theta/gradle processes, 6 idle processes total (`systemd --user`, and an
idle tmux "0" + bash created Jul 25 that predates this work). `systemd --user` was left alone (login
infrastructure, recreated at next login); **the tmux server was killed at the user's request**, so
session "0" and its bash are gone. Nothing of the user's now runs on sosy except `systemd --user`.

**Do not launch anything on sosy until the user says otherwise.** benchcloud is also off the table —
it was offline on 2026-08-04 and its run 82 never started. So the commits after `323c583fc7`
(backwards pointer steps, causes D/H/G, hex float constants) are **unmeasured** and will stay that
way until a host is available; keep gating locally with the canaries and per-task A/B sweeps.

**benchcloud is still unreachable** (connection to port 2222 times out, checked 2026-08-06), so the
stale run-82 job queued there could not be cleaned up. If that host returns, note that a 36602-run
job pinned to the old `Theta-svcomp-82` archive may still be sitting in its queue — decide then
whether to let it produce its (still-useful, batch-82-only) measurement or kill it.

### Run 84 vs run 80 — the comparison that matters most

Run 80 (benchcloud, Skylake, `theta27-long900.xml`, **same 900 s limit**) is a better yardstick than
run 79 for everything except host, because the time limit matches. All three, 36531 runs each:

| | run 79 (sosy, 300 s) | run 80 (benchcloud, 900 s) | run 84 (sosy, 900 s) |
|---|---|---|---|
| correct true | 7310 | 8157 | 8320 |
| correct false | 3550 | 4362 | 4445 |
| **WRONG true** | 23 | 35 | **21** |
| **WRONG false** | 59 | **358** | **61** |
| non-answer | 25589 | 23619 | 23684 |
| **SCORE** | 16490 | 13828 | **19437** |

**vs run 80: +5609, and wrong answers 393 → 82.** Nearly all of that is `WRONG false` collapsing
from 358 to 61 — the valid-deref overapproximation fix (the flat-model false-deref flood). That is
the single biggest result of this work so far, and unlike the run-79 delta it is *not* explained by
the time limit.

⚠️ There is **no full master baseline** — master was only ever run on the concurrency/userprop
subset (`baseline-master-22ab2b88de-oc-userprop`, 4 result files). Any "vs master" claim would have
to be made up. Run one if a real comparison is wanted.

### Run 84 non-answer breakdown (23684 total)

| status | run 79 | run 80 | run 84 |
|---|---|---|---|
| TIMEOUT | 16574 | 12326 | 12700 |
| **OUT OF MEMORY** | 2502 | 6497 | **6489** |
| ERROR (frontend failed, before parsing) | 3261 | 2348 | 2302 |
| ERROR (frontend failed, after parsing) | 1437 | 1603 | 1238 |
| `false(valid-free)` (scored as neither) | 0 | 362 | 362 |
| unknown | 341 | 379 | 357 |
| **ERROR (solver error)** | 53 | 66 | **198** |

Three things worth acting on:
1. **OOM is the second-largest bucket at 6489** — ~6.5k tasks scoring 0 on a 7 GB limit. It tracks
   the *time* limit, not this work (run 80 had 6497 at 900 s vs run 79's 2502 at 300 s): longer runs
   simply reach bigger states. Concentrated in `Juliet_Test` (2576), `hardness` (690),
   `eca-rers2012` (615), `neural-networks` (548). Probably the largest single lever left.
2. **Solver errors tripled** (53 → 198), concentrated in `uthash-2.0.2` (72) and `aws-c-common` (42).
   run 80 had 66, so this is new. The uthash tasks are the same ones a batch-82 frontend fix
   unlocked — worth checking whether unlocking them just moved the failure downstream.
3. **Frontend failures total 3540** (down from 4698 in run 79), concentrated in `intel-tdx-module`
   (727 across both phases), `ldv-linux-4.2-rc1` (353), `float-newlib` (265), `ldv-linux-3.14` (255),
   `goblint-regression` (302, all after parsing).

Scripts: `benchmark-results/compare_runs.py` (per-task moves + score);
`scratchpad/summary84.py`, `scratchpad/errfam.py` (headline table, status and family breakdowns).

---

## Frontend failure triage (run 84: 3540 task-runs, 2243 distinct files)

Split by phase — benchexec's tool-info decides on whether `ParsingResult Success` was printed:

| | task-runs | distinct .yml | distinct .c/.i |
|---|---|---|---|
| **before** parsing (the C frontend threw while parsing) | 2302 | 2091 | 1747 |
| **after** parsing (parsing succeeded, a later pass threw) | 1238 | 909 | 496 |

Disjoint — no task appears in both.

⚠️ **The `--backend NONE` probe cannot see after-parsing failures.** All 163 sampled "after" files
report `ParsingResult Success`, which is a tautology, not a result. That population needs a probe
with a real backend; the number below covers *before*-parsing only.

### Ranked causes, from a stratified 307-file sample (≥8 per family, 47 families)

| cause | files | % | est. task-runs |
|---|---|---|---|
| **`No such variable/macro` — ordinary identifier (self/forward-referencing initializer)** | 142 | **46.3%** | ~1065 |
| `No such variable/macro` — undeclared library/builtin fn (`memcpy`, `malloc`, `__builtin_*`) | 32 | 10.4% | ~240 |
| byte-addressed union (float member / multi-byte address) | 22 | 7.2% | ~165 |
| NullPointerException (various) | 21 | 6.8% | ~157 |
| `Field [x] not found, available fields are: []` — struct has **no** fields (opaque/unresolved) | 16 | 5.2% | ~120 |
| `Only variable-backed functions are callable` | 15 | 4.9% | ~112 |
| `typeof` over an unsupported expression | 12 | 3.9% | ~90 |
| PARSES-NOW — already fixed by the 5 commits after run 84 | 10 | 3.3% | ~75 |
| `Only structs expected here` | 9 | 2.9% | ~67 |
| `__builtin_va_arg` type resolution | 8 | 2.6% | ~60 |
| `Field not found` (struct *has* fields) | 8 | 2.6% | ~60 |
| `Not yet implemented (register)` | 7 | 2.3% | ~52 |
| `Non-array expression used as array!` | 4 | 1.3% | ~30 |

**#1 is fixed** (`54cb7bcfa5`): parse OK on that sample went **10 → 92 (+82), 0 regressions**.

Note when re-measuring: other causes *rise* after a fix, because a file that used to die at its
first unsupported construct now reaches the next one. Only "parses / does not parse" is a clean
metric; per-cause counts are not comparable across builds.

### Next, in value order
1. **Undeclared library/builtin functions** (~240). LDV preprocessing strips the glibc declarations,
   so `memcpy(...)` has no declarator at all — and `MemoryFunctionsPass` already models memcpy, the
   frontend just throws first. ⚠️ Must be the narrow "synthesize a declaration for a *known* library
   function on undeclared use". A blanket function pre-registration was tried earlier, broke 3 LDV
   canaries and converted 0/20, and was reverted.
2. **Byte-union float member** (~165) — design settled: a *constant* float store can have its exact
   IEEE-754 bytes computed at compile time (no `fpToIEEEBV`, no NaN round-trip). Reads stay refused.
3. **`register` storage class** (~52) — same one-line shape as the `static` fix in batch 82.
4. **`available fields are: []`** (~120) — an opaque/forward-declared struct losing its definition;
   likely one bug behind all 16 files, worth diagnosing before assuming.
5. Re-probe the **after-parsing** 496 files properly, with a backend.

Scripts: `scratchpad/probe.sh` (parse-only, records the failure signature per file),
`scratchpad/fefiles.py` (extract failing files from a results dir).

### Undeclared modeled memory functions (`03e48ca3f8`)

`memcpy`/`malloc`/`memset`/`free` used with **no declarator** (LDV `.i` files have the glibc headers
stripped) failed at the *callee identifier* — "No such variable or macro: memcpy" — taking the whole
frontend down long before `MemoryFunctionsPass`/`MallocFunctionPass`, which model those calls
exactly, ever saw them. ~10% of before-parsing failures (32 of the 307-file sample, ~240 task-runs).

Routed only for names a pass models *by name*: `malloc`, `free`, `realloc`, `memcpy`, `memmove`,
`memset`. **`alloca` excluded on purpose** — its return type is not carried in metadata the way
`malloc`'s is (`declareMallocReturnsPointer`), so a synthesized call would default to an `int`
return and truncate the pointer under LP64; it is declared in our `<stdlib.h>` model instead.

⚠️ **The guard is the whole point: `getVar(name) == null`.** A program supplying its own `malloc` or
`memcpy` — LDV stubs routinely do — must keep it. That is what makes this safe where the earlier
blanket function pre-registration was not (it broke 3 LDV canaries, converted 0/20, was reverted).
Both directions have fixtures.

Method note worth keeping: my first "own definition wins" fixture leaned on pointer identity with a
global array and came back **Unsafe with *and* without** the change — a pre-existing modelling limit,
not a regression. A/B-ing it before believing it is what stopped a false alarm being shipped as a
fixture. Replaced with a call-counter form.

### Batch 84 running total (all local A/B, none benchmarked yet)

| fix | commit | measured |
|---|---|---|
| self/forward-referencing initializers | `54cb7bcfa5` | parse 10 → 92 of 307 (+82), 0 regressions; 46% of before-parsing failures |
| `register` / `auto` storage classes | `07f4cf2857` | 8 of 10 affected files parse |
| narrow memory cell reads | `c44d7b2f36` | run-84 regression `openbsd_cstrncmp-alloca-1` Unsafe → Safe; guard set 2 FAIL → 1 FAIL |
| undeclared modeled memory functions | `03e48ca3f8` | frontend crash → Safe; own-definition case unaffected |

### Still open from the run-84 triage
- `ldv-races/race-2_2-container_of` and `race-3_2-container_of-global` — the other two genuine
  regressions. **Still not reproduced**: two attempts at 200 s and 600 s both timed out (the 600 s
  attempt was killed by a host restart). They only answer near 900 s. Their `main` is a plain
  block-local `struct my_data data;` — no VLA and no symbolic alloca — so cause J's probe is ruled
  out; cause F (memcpy cells) or a batch-82 change remains the candidate.

## Batch 85 — parse-only benchmark on benchcloud (launched 2026-08-07 13:14 CEST)

benchcloud came back; sosy remains off-limits. Launched a **parse-only** run first, as directed,
before spending a full verification run.

- tool dir `Theta-svcomp-85` (= HEAD `6bc3648656`), XML `xmls/theta27-parse.xml`
- output `results/Theta-svcomp-85/theta27-parse.xml/2026-08-07_13:14:33/`, screen `theta-parse85`
- `--vcloudPriority IDLE` (as directed), `--vcloudCPUModel Skylake` (run 80's hardware),
  `--vcloudClientHeap 8192`
- gated first: canaries `parse` all green, fixtures 50 PASS / 0 FAIL

`xmls/theta27-parse.xml` is `theta27-short.xml` with `--portfolio STABLE` swapped for
`--backend NONE`; every other limit and all 8 rundefinitions are unchanged, which matters because
the recent frontend fixes are **gated on the memory-safety properties** and would be invisible in a
single-property run.

**Why this run is worth a slot.** With no backend the tool-info's exit-code mapping turns every task
into a pure frontend verdict — exit 0 → `unknown` (parsed), exit 210 → `ERROR (frontend failed,
before|after parsing finished)`. Two things follow:

1. It measures the frontend over all 36,602 task-runs instead of a 307-file sample, so the cause
   ranking stops being an extrapolation.
2. **It sees the `after parsing` failures, which a local `--backend NONE` probe structurally cannot.**
   That was the flaw in my earlier probe: with the backend off, an after-parsing failure never gets
   the chance to happen, so all 163 sampled files trivially reported "parses now". The 496
   after-parsing files have therefore never been measured. In the *benchmark* the pass pipeline does
   run, so exit 210 with `after` is reported honestly.

Analysis script: `benchmark-results/parse_summary.py <results-dir> [--by-family] [--files <substr>]`.

A full verification run follows only if this one looks clean — it is the cheaper way to find out
whether HEAD regressed the frontend anywhere.

### Re-ranking the frontend causes against HEAD (117 files, throw sites captured)

The run-84 ranking was measured at `323c583fc7`; four fixes have landed since, so I re-probed the
same stratified sample against HEAD. This time the probe captured the **throw site**, not just the
exception class — the earlier `NullPointerException` bucket had no message and collapsed 21 files
into one uninformative row.

Sample counts are **not** proportional (the sample is 8 files per family, so small families are
over-represented); the `weighted est.` column scales each bucket by its family's true size. Treat
these as directional only — batch 85's parse-only run replaces them with exact counts.

| bucket | sample | weighted est. files |
|---|---|---|
| byte-addressed union with a floating-point member | 17 | ~298 |
| `Field [x] not found, available fields are: []` (opaque struct) | 4 | ~67 |
| `__builtin_va_arg` over an unresolvable `typeof` | 8 | ~41 |
| function-pointer call ("Only variable-backed functions are callable") | 7 | ~38 |
| `&malloc` / attribute-in-parens declarator (goblint-coreutils) | 8 | ~24 |
| `__builtin_inff` / `huge_val` | 6 | ~20 |
| dimensionless array `T a[] = {…}` NPE | 10 | ~18 |
| `__builtin_popcountl` | 2 | ~9 |
| `__builtin_prefetch` | 3 | ~8 |

**Two conclusions overturn earlier ones, and one confirms an earlier call.**

1. **The NPE bucket is a single site** — `FunctionVisitor.java:1354`, `List.of(allocaSize)` with a
   null dimension, i.e. the dimensionless array `T a[] = {…}`. That is the fix already sitting in
   `stash@{0}`, measured at **net −32** and parked. So the largest NPE bucket is a known, priced,
   deliberately-deferred item rather than a new bug. Left parked; batch 85 will say what it is worth.

2. **The union/float bucket is ~298 files, not the 2 tasks I priced it at.** My earlier estimate came
   from the run-84 *wrong-result* triage, which only ever saw the two tasks that got far enough to
   answer; it could not see the hundreds that die in the frontend. The estimate was wrong by two
   orders of magnitude and the decision deserved re-opening.

   **The decision does not change, and the reason is worth stating.** The files are
   `inv_sqrt_Quake`, `cast_float_union`, `float-newlib/*` — float↔int *type punning*, which needs
   exactly the `fpToIEEEBV` round-trip that batch 59 closed as unsound. It is not an incidental
   refusal that a small patch removes; it is the byte-granular memory model. And the scoring makes
   guessing actively dangerous: 298 files currently score **0** as errors, whereas an unsound
   round-trip that answers confidently costs −16/−32 each. This bucket is now the single strongest
   argument for the byte-granular memory model, and it should be sized against that project rather
   than patched.

3. `&malloc` in goblint-coreutils is **not** a gap in the undeclared-memory-function fix — those
   files take the *address* of `malloc` (`(void *(*)(size_t))(& malloc)`) and additionally spell its
   declarator as `void *(__attribute__((...)) malloc)(size_t)`. Same family as the function-pointer
   bucket, out of that fix's scope by design.

### GCC builtins with no declaration (batch 85)

`__builtin_*` names have no declarator in a preprocessed source, so the *callee identifier* fails to
resolve ("No such variable or macro: __builtin_inff") and the whole file dies in the frontend before
anything else runs. `handleBuiltinCall` already had the dispatch point; these names simply were not
in it. Added, all with exact semantics:

| builtin | model |
|---|---|
| `__builtin_inf` / `inff` / `infl`, `__builtin_huge_val*` | `+inf` literal of that width |
| `__builtin_nan` / `nanf` / `nanl` | quiet NaN of that width (payload string ignored) |
| `__builtin_isgreater(equal)`, `isless(equal)`, `islessgreater`, `isunordered` | alias to the plain names `FpFunctionsToExprsPass` already models |
| `__builtin_isnan`, `__builtin_isfinite`, `__builtin_finite` | alias to `isnan` / `isfinite` |
| `__builtin_prefetch` | dropped; operands still evaluated |

Nothing here is an approximation: infinity and NaN are exact values, the comparisons already had
exact models under their plain spelling, and `__builtin_prefetch` genuinely has no semantics. The
NaN *payload* is the one thing discarded, and it is unobservable — reading it needs the bytes of a
floating-point union member, which is refused outright.

Two traps worth recording:

- **`__builtin_inf` ends in `f` but is the `double` one.** Deriving the width from the name's last
  character — which reads as the obvious implementation — silently returns a `float` infinity for it.
  The names are spelled out instead, and the fixture checks `__builtin_inf` against a value only a
  double infinity exceeds.
- **`__builtin_prefetch`'s operands are still evaluated.** The hint has no effect, but
  `__builtin_prefetch(&a[i++])` must still increment `i`. Dropping the whole call, which is the
  tempting one-liner, would silently discard the side effect; the fixture pins it — **and caught a
  real bug in the first version of this fix.** I copied the `__builtin_va_start` case, which
  evaluates operands via `arg.accept(functionVisitor)`; that parses the operand but drops its side
  effect, so `i` stayed 0 and the fixture went UNSAFE. Operands must go through
  `arg.accept(this)` — the *expression* visitor is what emits side-effect statements — which is what
  `__builtin_expect` next to it already did. The `va_start` case has the same latent flaw but is
  harmless there: C requires those operands to be an lvalue and a parameter name, so they cannot
  carry side effects. Left alone rather than widened.

**Measured — and then corrected.** Of the 1747 before-parsing failures, 272 files (15.6%) use one of
these builtins. My first number, "6 of 30 now parse", was **wrong**: the probe called a file parsed
whenever `ParsingResult Success` appeared in the output, but theta prints that marker and can still
fail in a later stage and exit 210. Re-measured with the **exit code** — which is what benchexec's
tool-info actually keys on — it is **2 of 30** that fully succeed.

What does hold, and is the point of the fix: **zero files remain blocked on any `__builtin_` name**.
The other 28 fail on causes that were always sitting behind the builtin.

⚠️ **Every "parses now" figure in this file measured before 2026-08-07 has the same flaw** and is an
over-count. Use `scratchpad/probe_rc.sh` (exit-code based) for anything new. The docstring claimed `isnan`/`isfinite` were already aliased when only `isinf` and
`isnormal` actually were, so that gap is closed too.

Fixtures: `builtin_infinity.c`, `builtin_nan_compare.c`, `builtin_prefetch.c`.

### Next target: the opaque-struct bucket, narrowed to one struct

Of the remaining `Field [x] not found, available fields are: []` failures, **12 of 13 are the same
field, `driver_data`**, and the accessed struct is `struct device_private`. In
`…vmxnet3.cil.i` the ordering is: forward declaration at char 23805 → `struct device` (which holds
`struct device_private *p`) at 27076 → the real definition of `device_private` at 180856 → the use
`(dev->p)->driver_data` at 496895. So the tag is completed long before it is used, and
`visitCompoundDefinition` already has the "complete a field-less forward declaration rather than
replacing it" path that this should exercise.

**Three minimal repros of that shape all parse fine**, so none of my theories is the bug:

1. plain forward declaration completed later — parses;
2. plus a *self-referential* `struct device` (`struct device *parent`), to force
   `Struct.getActualType`'s `currentlyBeingBuilt` → "self-embedded structs! Using long as a
   placeholder" path — parses;
3. plus `sizeof(struct device)` before the completion, to force the field list to be expanded and
   **cached** (`cachedActualFields`) while `device_private` was still empty — parses.

Theory 3 is worth restating even though it failed, because it is still the only mechanism that
explains an *empty* struct rather than an int placeholder: `cachedActualFields` is invalidated by
`addField` only on the struct whose own fields changed, so a struct that expanded a
still-incomplete member type would keep that empty expansion forever. It simply is not what these
files trigger — `sizeof` did not force it.

Confirmed from the real file (INFO log): the self-embedded placeholder path *does* fire (once), and
the failing access is `(dev->p)->driver_data`, with `struct device_private` defined at char 180856,
long before the use at 496895.

**ROOT CAUSE FOUND — by instrumentation, after four failed repros.**

The diagnostic (tag added to the message) first ruled out half the space: the real file reports
`Field [driver_data] of struct device_private not found, available fields are: []` — the *right*
struct, genuinely empty. A fourth repro (by-value embedding, which the real file does at
139307–145981, before the completion at 180856) still parsed, so I stopped writing repros and traced
`Struct.addField` / `getActualType` on the real file instead:

```
getActualType device_private  canonical=950689790  fields=[]           cached=null   <- expanded EMPTY
getActualType device_private  canonical=950689790  fields=[]           cached=0      <- reuses the empty expansion
getActualType device_private  canonical=950689790  fields=[]           cached=0
getActualType device_private  canonical=950689790  fields=[]           cached=0
addField      device_private.driver_data on 950689790                                <- definition finally arrives
getActualType device_private  canonical=950689790  fields=[driver_data] cached=null
```

`device_private` is expanded into an **empty `CStruct` four times before its definition arrives**.
`addField` correctly invalidates its *own* cache (the last line shows `cached=null`), but the empty
`CStruct` objects handed out by those four expansions were already embedded in **enclosing** structs'
`cachedActualFields`, and nothing invalidates those. So `struct device`'s field `p` stays a pointer
to a field-less struct for the rest of the parse. This is theory 3 after all — the repros failed only
because in each of them the *enclosing* expansion happened after completion, never before.

Confirms it is **one bug**, matching the bucket's homogeneity (12 of 13 failures are the same field).

**Fix, and the trap in it.** The obvious fix — a global generation counter bumped by every `addField`,
with caches valid only for the current generation — is correct but risks re-introducing exactly what
the cache was added to prevent: during the declaration phase every `addField` would invalidate every
cache, and the comment on `cachedActualFields` records that unbounded re-expansion is *exponential in
nesting depth* and "large LDV kernel headers ran out of heap inside it". The safer shape is to **not
cache an expansion that contained an incomplete (field-less) named struct**, leaving it to be
recomputed once the tag is complete; complete expansions still cache, so the steady state keeps
today's performance. Before implementing, check whether `CDeclaration.getActualType` also memoises
the stale type — invalidating only `Struct`'s cache is not enough if it does. Needs the full canary
gate plus a timing check on a large LDV file, since the failure mode of getting it wrong is a heap
blowup rather than a wrong answer.

**Second, distinct bug found in the same family** (`Only structs expected here, got …complex.integer…`,
forester-heap + 3 LDV files): `getActualType`'s self-embedded guard returns `signedInt` wrapped in
the field's pointer levels, so `struct device *parent` resolves to **`int*` rather than
`struct device*`**. A pointer to a struct under construction needs no recursion at all — a pointer is
a scalar of known size — so the placeholder fires far too eagerly. Only genuine *by-value*
self-embedding is illegal in C and needs the placeholder.


### Struct cache fix — measured honestly (batch 85)

The `cachedActualFields` fix (see the root-cause section above) works: across the 13 known
opaque-struct files the `Field [x] … available fields are: []` error class is **gone entirely**. But
the benchmark value is far smaller than the bucket size suggested — re-measured by exit code:

| outcome with the fix | files |
|---|---|
| fully succeeds (exit 0) | **1** |
| `Could not handle left-hand side of assignment` (FrontendXcfaBuilder:1416) | 6 |
| `ClassCastException` (bv_zero / deref typing) | 4 |
| timeout at 150s | 2 |

All 13 scored 0 before as frontend errors, and 12 still score 0 as *different* frontend errors. So
this is worth ~1 file today. It is still worth shipping: an empty struct type is silently **wrong
modelling**, not merely a refusal, and wrong types are exactly the thing that produces wrong verdicts
rather than honest errors. But it should be booked as unblocking, not as points — and
`Could not handle left-hand side of assignment` is now the top blocker in this family, having been
hidden behind the struct bug in 6 of 13 files.

**No canary guards it.** Both real files I added were rejected by the suite and removed:
`vmxnet3` does not fully parse even with the fix (it advances to the left-hand-side error), and
`pktcdvd` is OOM-killed under `theta-start.sh`'s hardcoded `-Xmx14210m` in this host's 8 GB cgroup —
and running two files that heavy 4-way parallel also OOM-killed an unrelated canary
(`cartpole_0_safe`), which is a good reminder that a heavy canary damages its neighbours. Five
minimal repros all parse identically with and without the fix, so the fix is validated only by the
direct A/B recorded above (`THETA_NO_DEPINVAL`, both files flipping cleanly at `-Xmx4g`).

## Batch 85 RESULTS — the parse-only run (complete, 72,103 task-runs)

Finished 2026-08-07 ~14:30 CEST. This is the first measurement of the frontend over the *whole*
benchmark rather than a sample, and the first that can see after-parsing failures at all.

| status | runs | share |
|---|---|---|
| `unknown` (parsed, XCFA built) | 62,049 | **86.1%** |
| ERROR (frontend failed, **before** parsing) | 3,753 | 5.2% |
| OUT OF MEMORY | 2,603 | 3.6% |
| ERROR (frontend failed, **after** parsing) | 2,502 | 3.5% |
| TIMEOUT | 1,186 | 1.6% |

**13.9% of the benchmark cannot even be handed to a backend**, and a third of that is resource
exhaustion *while parsing* — 2,603 OOM and 1,186 timeouts with no verification work being done at
all. That bucket was completely invisible before this run.

### The ranking this produces — it is not the one I was working from

| family | non-parsing runs | kind |
|---|---|---|
| **intel-tdx-module** | **1,634** | 688 before + 814 after + 132 OOM |
| eca-rers2012 | 852 | 800 **OOM** |
| hardware-verification-bv | 780 | 704 **TIMEOUT** |
| ldv-linux-4.2-rc1 | 764 | mixed |
| ldv-linux-3.14 | 638 | mixed |
| float-newlib | 530 | the union/float-punning wall |
| goblint-regression | 507 | **all after-parsing** |

Three things this overturns:

1. **`intel-tdx-module` is the single largest frontend blocker by a wide margin, and I have never
   looked at it** — it did not stand out in the stratified sample because that sample took 8 files
   per family regardless of family size. It is both the largest before-parsing *and* the largest
   after-parsing family.
2. **`goblint-regression` (507) is entirely after-parsing**, so no local `--backend NONE` probe could
   ever have seen it. Same for most of `pthread-*`.
3. **`eca-rers2012` OOM (800) and `hardware-verification-bv` TIMEOUT (704) are resource problems, not
   missing features.** No amount of grammar work touches them; they need the frontend to be cheaper.
   Worth noting next to the struct-cache work: that cache exists precisely because this expansion is
   exponential, and 2,603 parse-time OOMs say the cost problem is real and unsolved elsewhere too.

Next targets, in this order: `intel-tdx-module` (one family, 1,634 runs, cause unknown),
`goblint-regression` (507, one cause worth identifying), then the parse-time OOM/TIMEOUT families.

### Two methodology bugs found while acting on the batch-85 ranking

**1. My yml→input-file extractor silently dropped whole families.** It matched
`input_files:\s*'([^']+)'` — requiring single quotes. `intel-tdx-module`'s ymls write
`input_files: name.i` bare, so **the single largest failing family was absent from every local
sample I ever built**, which is why it never appeared in any ranking before the benchmark produced
one. Accept quoted *or* bare.

**2. "--backend NONE cannot see after-parsing failures" was wrong.** I stated this as the
justification for the parse-only run. Probing 8 intel-tdx after-parsing files locally with
`--backend NONE` reproduces **8 of 8** — theta prints `ParsingResult Success`, then fails building
the XCFA, and exits 210. What actually hid them was the probe's success criterion (marker string
instead of exit code), the same flaw that inflated the "parses now" counts. The parse-only run was
still the right call — it gives complete, correctly weighted counts over 72k runs rather than a
skewed sample — but not for the reason given.

### Top after-parsing cause: bitfield assignment (`FrontendXcfaBuilder`)

`Could not handle left-hand side of assignment` is the largest single after-parsing cause found so
far: 6 of 8 in the intel-tdx sample, 6 of 13 in the opaque-struct files, 10 of 14 combined.

The old message interpolated the `CAssignment`, whose `toString` is `CAssignment@4f8b199b` — it
names the failure but not the construct, collapsing an entire family into an unclassifiable bucket.
Naming the shape instead identified it immediately:

```
lhs is a BvZExtExpr
  [ bv_zero_extend(bvpos(bv_zero_extend(extract(deref(error_code, …, Bv 8), 5, 6), Bv 8)), Bv 32) ]
  of type (Bv 32), rhs type (Bv 32)
```

An `extract(…, 5, 6)` over a dereferenced byte: a **bitfield store**. The read path builds
`extract`, and the write path then has an `extract` — not a location — on the left. A bitfield write
needs read-modify-write: read the containing byte, clear the bit range, or in the shifted value,
write the byte back. Reads already work, so the layout information needed (offset, width) is
present.

Worth doing next: it is the top after-parsing cause, it is one well-understood mechanism rather than
a family of special cases, and `intel-tdx-module` alone has 407 after-parsing files.

#### …and the bitfield store is not missing — its metadata is lost

Reading further: `FrontendXcfaBuilder` **already implements** the read-modify-write store
(`BitfieldSlice.write`, line ~1299). It finds the target by looking up `BitfieldSlice.CELL`
metadata on `lValue`:

```kotlin
val bitfieldCell =
  parseContext.metadata.getMetadataValue(lValue, BitfieldSlice.CELL).orElse(null)
    as? Dereference<*, *, *>
```

`FrontendMetadata` is **identity-keyed**. The read path stamps CELL/OFFSET/WIDTH on the object it
returns — `declaredType.castTo(BitfieldSlice.read(cell, ...))` — but the left-hand side that
reaches the builder has been wrapped further:

```
bv_zero_extend( bvpos( bv_zero_extend( extract(deref(...), 5, 6), Bv 8)), Bv 32)
                 ^^^^^  ^^^^^^^^^^^^^^ extra wrapping around the stamped object
```

so it is a *different object*, the lookup returns null, and it falls through to the error. **The
feature works; the metadata does not survive re-wrapping.** Same identity-keyed-metadata trap that
loses `cType` on rebuilt expressions.

Two candidate fixes, in preference order:
1. Find what wraps the lvalue after the member access and stop it wrapping the *assignment target*
   (the conversion is meaningful for an rvalue read, not for a store target). Narrowest, but needs
   the wrap site identified.
2. Failing that, unwrap benign wrappers (`BvZExtExpr`/`BvSExtExpr`/`bvpos`) in the builder before
   the CELL lookup and retry. Broader, and risks accepting an lvalue that genuinely *was* converted.

Do NOT start by writing a bitfield read-modify-write — it already exists, and rewriting it would
duplicate working code while leaving the actual defect in place.

### Item 3 (byte-union float member): premise confirmed, and the one hazard to design around

Both tasks are exactly as described — the float member is written with a **compile-time constant**
and never read:

```c
union X { int y; double z; };
var.z = 0x1.4p+4;                  /* constant; the only use of z */
var.y = 10u;                       /* overwrites the same storage */
__VERIFIER_assert(var.y == 10u);   /* only y is ever read */
```

So the exact IEEE-754 bytes are computable at parse time and no `fpToIEEEBV` round-trip is needed.
Worth +4 (2 tasks).

**The write machinery already exists.** `FrontendXcfaBuilder` handles byte-union member stores via
`ByteUnionSlice.BASE` metadata — "the right-hand side is split into its own one-byte cells and each
is written outright". A float member is refused earlier, at *access* time in
`byteLaidOutMemberAccess`, because a **read** would need the round-trip.

⚠️ **The hazard, which is why this is not a five-minute change.** Access is one call serving both
reads and writes. Returning a marker for the float member so the store path can see it means the
same marker is returned when the member is used as an *rvalue*, and it would then silently evaluate
to a wrong value — in the very path gated for NaN soundness. A silent wrong read is worth −32 where
the current refusal is worth 0, so the naive version is a bad trade even though it "works" on these
two tasks.

Any implementation must make a read of that marker **fail loudly**, not merely be discouraged. Two
shapes worth considering: intercept at the *assignment* level in `FunctionVisitor` so no marker ever
escapes into an expression; or return a marker that carries no usable value and have every rvalue
consumer throw on it. Do not ship the version that only special-cases the store and leaves reads
returning the marker.

#### Bitfield store: the metadata is gone entirely, not merely wrapped — tried and reverted

Traced the real failure (`intel-tdx-module/tdh_mng_init__…_havoc_object.i`) with a temporary probe in
the builder's fallthrough:

```
TRACE lhs=BvZExtExpr CELL=ABSENT OFFSET=ABSENT cellExpr=null
```

**`BitfieldSlice.CELL` is absent on the lvalue**, so the earlier reading — "the stamp is on an inner
node under an integer promotion" — is wrong. I implemented that fix anyway (`sliceCarrier`, peeling
single-operand wrappers and retrying the lookup): the intel-tdx file **still failed identically**,
so nothing on the ancestor chain carries the metadata either. The expression is rebuilt wholesale
somewhere between the member access and the assignment, and identity-keyed metadata does not survive
a rebuild. Reverted — it was unvalidated code with no measured effect. A plain pointer-to-bitfield
store (`p->f = 1`) parses fine both before and after, so the simple path was never broken.

**The promising direction is structural, not metadata-based.** The left-hand side is

```
bv_zero_extend( bvpos( bv_zero_extend( extract(deref(cell…), 5, 6), Bv 8)), Bv 32)
```

and an `extract` *carries its own offset and width* (5, 6) with the cell as its operand. So the
builder can recognise the shape directly — peel the extends, match `BvExtractExpr` over a
(possibly `Pos`-wrapped) `Dereference`, and reconstruct the read-modify-write from the extract's own
bounds — with no reliance on metadata surviving. Needs care over signedness and the cell's C type,
and must not intercept a genuine rvalue extract.

Do not retry the metadata-lookup variants: the stamp is not there to be found.

## Batch 86 RESULTS — full run at HEAD (finished 2026-08-08 14:36 CEST)

`results-run86/`, launched at IDLE priority on benchcloud with `theta27-long900.xml`, CPU pinned to
Skylake — deliberately the same host, XML and CPU model as **run 80**, so the comparison is not
confounded by hardware or time limit. Tool dir `Theta-svcomp-86` = `03b1089b94`.

| | run 80 | run 86 | delta |
|---|---|---|---|
| SV-COMP score | 13,828 | **19,516** | **+5,688** |
| correct | 12,519 | 12,815 | +296 |
| error | 22,869 | 23,314 | +445 |
| unknown | 750 | 337 | −413 |
| **wrong** | **393** | **65** | **−328** |
| correct true / false | 8,157 / 4,362 | 8,061 / 4,754 | −96 / +392 |
| wrong true / false | 35 / 358 | 20 / 45 | −15 / −313 |

**Zero regressions** (nothing correct in run 80 became wrong). The gain is almost entirely
**wrong-false collapsing 358 → 45**, i.e. the valid-memsafety false-deref flood is gone — that
family was the batch-63 blocker and it is now closed at scale. Unlike run 84, none of this is a
time-limit artefact: run 80 was already at 900 s.

For reference against run 84 (sosy, 5750G): score 19,437 → 19,516 and wrong 82 → 65. Directionally
positive but **not a clean comparison** — different host and CPU model — which is exactly why run 86
was pinned to run 80's hardware instead.

### The one thing to triage: 20 newly-wrong-from-non-answer

No task regressed from correct, but 20 went from error/timeout to a *wrong* answer, which costs
points where an error cost nothing (−16/−32 vs 0). Most are frontend fixes doing their job and
handing a now-parsing task to a backend that then gets it wrong:

- `memsafety/test-0214,-0217,-0218,-0232-2`, `list-ext-properties/test-0214_1,-0217_1,-0232_1-2`:
  `frontend failed, before parsing` → **`false(valid-deref)`**. One family, one likely cause.
- `uthash-2.0.2/uthash_JEN_nondet_test2-2`, `-test4-3` (both memcleanup and memsafety):
  `frontend failed, after parsing` → `false(valid-deref)`.
- `ldv-memsafety/ArraysOfVariableLength{,2}`, `pthread-complex/workstealqueue_mutex-2`: TIMEOUT →
  `false(valid-deref)`.
- `floats-cbmc-regression/float-rounding1`, `float-to-double2`: frontend → `false(unreach-call)`.
- `aws-c-common/aws_linked_list_{node_reset,remove}_harness`: OOM → `false(unreach-call)`.

The `test-021x` / `list-ext-properties` group is the obvious first target: 7 tasks, one property,
one transition, and they only started answering because the frontend stopped refusing them.

### ROOT CAUSE of the run-86 `test-021x` newly-wrong family: arrays declared through a typedef

The 7 newly-wrong `memsafety/test-0214,-0217,-0218,-0232-2` + `list-ext-properties/test-0214_1,
-0217_1,-0232_1-2` tasks are **not** a shape-analysis limitation. `test-0214` reproduces locally in
**4.6 seconds with `Trace length: 7`** — far too short for a doubly-linked-list precision problem —
and bisects to a four-line repro:

| declaration | valid-memsafety verdict |
|---|---|
| `int arr[2];` | Safe |
| `void *arr[2];` | Safe |
| `static int arr[2];` | Safe |
| **`typedef int arr_t[2]; arr_t a;`** | **Unsafe (valid-deref)** |
| **`typedef void *p_t[2]; p_t a;`** | **Unsafe (valid-deref)** |
| **`typedef void *p_t[2];` … local `p_t a;`** | **Unsafe (valid-deref)** |

**Any array declared through a typedef loses its extent**, so the very first element read fails the
`ptr_size` bound check. Element type and storage duration are irrelevant; only the typedef matters.
Every one of these 7 tasks declares its list as `typedef ... list_t[2]; list_t list;`.

Not a decay-to-pointer: `sizeof(typedef array) == sizeof(plain array)` verifies Safe, so the type
really is a `CArray` with its dimension intact. The alloca emission in
`FunctionVisitor#visitBodyDeclaration` is gated on `declaration.getActualType() instanceof CArray`,
which a typedef'd array *does* satisfy — so the loss is somewhere after that, and the next step is
to **diff the serialized XCFA** (`--enable-c-serialization`, unreach-call only) between the typedef
and non-typedef locals rather than reason about it further.

Note `CDeclaration.getArrayDimensions()` (the *declarator's* `[2]`) is empty for `p_t a;` while the
*type's* dimension is present — a likely shape for the bug, and worth checking first.

**Value:** −112 points today (7 tasks × −16), and these tasks only began answering because the
frontend stopped refusing them, so this is the direct cost of the frontend fixes landing. Likely
affects more than the 7, since typedef'd arrays are a common idiom. Fixing it should convert them to
correct `true` rather than merely back to errors.

#### Mechanism and fix design (typedef'd arrays)

Serialized-XCFA diff between `int a[2]` and `typedef int arr_t[2]; arr_t a` inside `main`
(`--enable-c-serialization`, unreach-call):

```
  plain                                   typedef
  int_arr main__a;                        long main__a;          <- a SCALAR, not an array
  long call_alloca_ret0;                  (absent)
  __malloc = 3;                           (absent)
  call_alloca_ret0 = (__malloc + 1);      (absent)
  main__a = (+ call_alloca_ret0);         (absent)               <- no object, so no extent
```

The variable is not created as an array and **no `alloca` is emitted at all**, so the object has no
`ptr_size` entry and the first element read fails the bound check. `sizeof` is nevertheless correct
because it is computed from the type independently.

**Why:** an array's dimensions live on the **declarator** (`CDeclaration.arrayDimensions`), not on
the type. `typedef int arr_t[2]` therefore records `[2]` on the *typedef's own CDeclaration*, while
`TypedefVisitor.getSimpleType(id)` — what `TypeVisitor#resolveTypedefName` hands to a later
declaration — returns `CDeclaration::getType()`, the `CSimpleType`, which never carried it. So
`arr_t a;` sees a plain scalar type. (`getType(id)`, returning `getActualType()`, *does* carry it —
which is why `sizeof` is right and the `instanceof CArray` gate looked satisfied.)

**Fix — follow the existing precedent.** `markFunctionPointerTypedefs` already solves exactly this
shape for `typedef int (*handler)(int)`: it copies declarator-level function-pointer-ness onto
`declaration.getType()` so later users inherit it. Do the same for dimensions:

1. `CSimpleType`: hold the typedef's array dimensions (alongside `functionPointer`); include them in
   `copyOf()`, which `resolveTypedefName` relies on.
2. `TypedefVisitor`: a `markArrayTypedefs` pass beside `markFunctionPointerTypedefs`, copying a
   typedef declaration's `getArrayDimensions()` onto its type.
3. Where a declaration is built from a resolved typedef, append the typedef's dimensions **after**
   the declarator's own. Order matters and is easy to get backwards: in C,
   `typedef int A[2]; A x[3];` makes `x` an `int[3][2]`, i.e. the declarator's `[3]` is outermost.

Gate on the four-line repros above (plain/static/typedef × global/local, all must be Safe), the 7
run-86 tasks, and a fixture pinning both the extent *and* the dimension order for `A x[3]`.

#### Fix shipped — and what it actually bought (measured, not predicted)

Implemented as designed: dimensions carried on `CSimpleType` (and through `copyOf()`, which the
typedef resolution relies on), a `markArrayTypedefs` pass beside `markFunctionPointerTypedefs` at
both call sites, and inheritance appended **after** the declarator's own dimensions.

Repro level — all pass, control unchanged:

| shape | before | after |
|---|---|---|
| `typedef int[2]` global / `void*[2]` global / `void*[2]` local | Unsafe (valid-deref) | **Safe** |
| plain `int[2]`, `void*[2]`, `static int[2]` (controls) | Safe | Safe |
| `typedef int A[2]; A x[3]` — `sizeof(x[0]) == sizeof(plain[0])` | — | **Safe** |

⚠️ **The 7 tasks it was supposed to fix are NOT fixed. My prediction above was wrong.**

| task | before (run 86) | after (local, 400 s) |
|---|---|---|
| `test-0214`, `-0217`, `-0218`, `test-0214_1`, `-0217_1` | `false(valid-deref)` | **no answer (timeout)** |
| `test-0232-2`, `test-0232_1-2` | `false(valid-deref)` | **still `false(valid-deref)`** |

**0 of 7 correct.** What the fix actually did for five of them is remove an *immediate* spurious
counterexample, so they now have to do real verification work — which does not finish in 400 s
locally. Whether they finish inside the benchmark's 900 s is unknown from here; locally it is 0
instead of −16 each, and would be +2 each only if they complete. Do not book either number without a
run. The two `test-0232*` tasks are unchanged and need a **separate root cause**.

Shipped anyway on correctness grounds, not on those tasks: a typedef'd array silently becoming a
scalar with no object at all is wrong *modelling*, which is the class of defect that yields wrong
verdicts rather than honest errors, and it is guarded by a fixture A/B'd to fail without the fix
(`Safe` with, `Unsafe (valid-deref)` without).

### The `test-0232*` cause: a ternary does not short-circuit its dereference

The two tasks the typedef fix did not touch have their own bug, and it is a general one.

`test-0232-2` reproduces with **`Trace length: 6`** — again far too short for a shape-analysis
limit — on this line of `append`:

```c
item->data = (item->next) ? item->next->data : malloc(sizeof *item);
```

where `item->next` is legitimately NULL on the first append. Isolated:

| guard form | verdict |
|---|---|
| `(p->next) ? p->next->v : 42` | **Unsafe (valid-deref)** ← false alarm |
| `if (p->next) x = p->next->v; else x = 42;` | Unknown (no alarm) |

`visitConditionalExpression` already guards each branch's *statements* behind a `CIf`, but the
branch **values** both go into one `Ite`, so a dereference in the untaken branch is an
unconditional memory access and the memsafety instrumentation checks an access C never performs.
The equivalent if/else never misreported, which both proves the bug and dictates the fix: assign
each branch's value to a temporary *inside* the guarded branch and let the conditional's value be
that temporary. Afterwards the ternary and if/else forms agree exactly.

**Gated on `parseContext.isCheckMemsafety()`** — under any other property the `Ite` is left exactly
as it was (it selects the right branch, and reading the other is unobservable), so the XCFA is
unchanged there, per the standing instruction.

Measured: the repro goes Unsafe → Unknown (matching its if/else control), and `test-0232-2` loses
its fast wrong answer (it now needs real work and does not finish in 250 s locally). Fixture
`ternary_guarded_deref.c` A/B'd: Safe with the fix, `Unsafe (valid-deref)` without.

**Triage lesson worth reusing:** both false-alarm classes found today — typedef'd arrays losing
their extent, and this — presented as `false(valid-deref)` on heap-manipulating list benchmarks that
look like hard shape-analysis targets, and both had **6–7 step counterexamples**. Trace length is a
cheap first discriminator: a short trace on a "hard" program means a modelling bug, not imprecision.

### Bitfield store, attempt 2: structural recognition — also reverted, and now the shape is known

The structural fix the plan called for was implemented (peel the width/signedness wrappers, match
`BvExtractExpr`, take the cell and the bounds from the extract itself) and **measured at zero
effect**: the intel-tdx after-parsing sample is byte-for-byte identical before and after (6/8 still
`Could not handle left-hand side`). Reverted, like the metadata attempt before it — unvalidated code
that changes nothing does not ship.

Tracing the real lvalue shows why, and it is the useful result:

```
TRACE lhs=BvPosExpr peeled=BvExtractExpr from=0 until=52 src=BvConcatExpr srcWidth=64
      parts=[BvLitExpr:8, Dereference:8, Dereference:8, Dereference:8,
             Dereference:8, Dereference:8, Dereference:8, Dereference:8]
```

**These are not single-cell bitfields.** The field is **52 bits wide**, and its storage unit is a
64-bit value *assembled by concatenation* from **seven separate byte dereferences** plus a padding
literal. Both earlier designs assumed one cell:

- metadata lookup (attempt 1): CELL absent everywhere — the expression is rebuilt;
- structural single-cell match (attempt 2): correctly refuses, because the field spans 7 cells.

**What it actually needs** is a multi-cell read-modify-write: splice the value across every byte
cell the field covers and write each one back, leaving the untouched bytes alone. The machinery
exists next door — the `ByteUnionSlice.BASE` branch already splits a right-hand side into byte
values and writes each cell — so this is a generalisation of that, not new ground.

⚠️ **The hazard that decides whether it is worth doing.** The mapping from concat position to byte
*address* must be exactly right: `Concat`'s first operand is the HIGH bits, and the derefs are at
increasing addresses, so the order is reversed relative to the operand list. Getting it backwards
writes the right bits to the wrong bytes — a silently wrong value, not a refusal, on 407
intel-tdx-module files. That is the −32-per-task failure mode the batch exists to avoid, so this
needs a fixture pinning the byte order (write one field, read back a *neighbouring* one) before any
of it ships.

### Bitfield store, attempt 3: multi-cell — SHIPPED

The shape (established by tracing, see above) is a field wider than one cell whose storage unit is
assembled by `Concat` from several byte dereferences. The store now splices the value across every
cell the field overlaps and writes those cells back.

**The byte-order hazard is avoided rather than reasoned about.** Instead of deriving byte addresses,
the writer takes the mapping straight from the `Concat` that the *read* path built — each operand is
a cell at a known bit range, and the read path is correct — so endianness is inherited, never
recomputed. Only overlapped cells are written, so untouched neighbours are not rewritten (a spurious
write would also invent a data race under no-data-race).

**Measured, per file, on the intel-tdx after-parsing sample:**

| outcome | before | after |
|---|---|---|
| `Could not handle left-hand side` | 6 | **2** |
| fully succeeds (exit 0) | 0 | **2** |
| advanced to a later error (ClassCastException) | 1 | 3 |

Four files changed, **none regressed**.

⚠️ **No canary guards this, after five attempts — and that is a real gap, recorded deliberately.**

- Four minimal fixtures (local wide bitfield; pointer-to-global; `p->` access; a union mirroring
  `pa_t`). The first three parse **identically with and without** the fix and would have guarded
  nothing. The union one fails **both** ways — so there is at least one further bitfield-store
  sub-shape this fix does *not* cover, and the 407-file bucket is not fully closed.
- Two real files (~160 KB) as canaries: they pass, but they OOM-killed a neighbouring canary
  (`cartpole_0_safe`, exit 137) in the 4-way parallel sweep, while passing in isolation. Removed —
  a gate that flakes costs more than one missing guard. Same call as the LDV canaries earlier.

The evidence standing in for a guard is the per-file A/B above, reproducible with
`scratchpad/probe_rc.sh` over `scratchpad/tdx_after.txt`.

**Why minimal repros keep failing here** (third time this session, after the struct cache): these
bugs live in composite frontend paths — byte-laid-out unions, concat-assembled units — that
hand-written C does not reach. The real shape only ever came out of tracing the actual input.

### intel-tdx-module before-parsing (344 files): blocked on the bytes memory model

Two causes in the 8-file sample: 5 × "Taking the address of a multi-byte member of a byte-addressed
union", 3 × "Referencing non-lvalue expressions is not allowed!".

The second was diagnosable once the message named the operand — it is `&` applied to
`bvpos(bvpos(zext(extract(deref(...), 0, 64))))`, a **full-width** extract, i.e. an expression that
does denote storage even though it is not syntactically an lvalue. I implemented the corresponding
fix (`&` of a whole-cell extract = the cell's address, restricted to full width so a genuine
bitfield — whose address C forbids — still refuses). **It worked**: all 3 files moved past the
check. They then land on the *first* cause, so the sample is now 8/8 on that one refusal.

**And that refusal is a model limitation, not an oversight.** Its own comment:

> the resulting pointer would have to know it reads several byte-cells as one value, which no
> pointer in this model can express. […] **Under the bytes memory model this restriction does not
> apply**: every object is a run of byte cells and a pointer is a plain byte address.

There is no standalone win either: `&u.raw` on a single 64-bit union member fails **identically with
and without** the change, because in a byte-laid-out union a cell *is* a byte, so any 64-bit member
spans eight of them. So the whole-cell fix converts one error into another and nothing more.

**Reverted the logic; kept only the improved diagnostic** (which is what made this diagnosable and
costs nothing). No measured benefit does not ship — the same rule applied to both earlier bitfield
attempts.

⚠️ **Strategic: two of the largest frontend buckets now converge on the same project.** This one
(344 before-parsing files) and the float↔int union-punning wall (~298 files) are both waiting on the
**byte-granular memory model**, already the designated next big task. Neither is reachable by
further local patching, and work in this area will keep hitting the same wall. That is a stronger
case for the bytes model than either bucket made on its own — and the whole-cell address-of fix
above is worth re-applying *once the bytes model lands*, since it will be a genuine unblocker then.

### goblint-regression (507 after-parsing runs): pthread handles passed by pointer

Cause identified, and it is **not** a parsing problem — all of it is `CLibraryFunctionsPass`
refusing the mutex handle. Sample of 10 files (103 distinct files behind the 507 runs):

| message | files |
|---|---|
| `Unsupported library parameter: expected reference base` | 4 |
| `Local mutex handles are not supported: <name>` | 4 |
| `Non-static mutex handles (multiple writes)` | 1 |
| `Unsupported library parameter: non-constant dereference` | 1 |

The name is misleading: these are not locally *declared* mutexes. The shape is a handle reached
through a **pointer parameter**:

```c
void munge(pthread_mutex_t *m, int *v) { pthread_mutex_lock(m); ... }
void *t1_fun(void *a) { munge(&mutex1, &global1); }
void *t2_fun(void *a) { munge(&mutex2, &global1); }
```

`checkMutexDecl` requires the handle to be a global `VarDecl`, because a pthread handle is an
**identity key** — the analysis maps the decl to a mutex identity. Here it resolves to the local
parameter `munge::m` instead of the global it points at, and refuses.

⚠️ **Do not "fix" this by collapsing the local to one identity.** Two different globals reach that
parameter, and the task is called `ptrmunge_racing` precisely because the verdict depends on telling
`mutex1` from `mutex2`. Merging them would invent or hide races — a wrong answer where there is
currently an honest error.

**The obvious design does NOT work — checked, not assumed.** It would be: after inlining, each copy
of `munge` has its own `m` written exactly once (`&mutex1` in one, `&mutex2` in the other), so a
local handle with a single definition naming a global mutex resolves soundly while the copies stay
distinct. But `ProcedurePassManager` runs **`CLibraryFunctionsPass` (line 55) before
`InlineProceduresPass` (line 79)**, so at the time the handle is read there is exactly one `munge`
with one parameter `m` and no definition at all — the design's premise is false.

That leaves three routes, none of them small:
1. **Move `CLibraryFunctionsPass` after inlining.** Cheapest to try, but the ordering is deliberate:
   the comment above it requires an array element index to be constant *before* the pass reads the
   handle, so moving it needs that constraint re-checked.
2. **Interprocedural candidate sets** — resolve the parameter to the set of globals reaching it, and
   keep them distinct (the actual "candidate sets for pthread handles" task).
3. **Per-call-site specialisation** of procedures that take a handle parameter.

Whichever is chosen, the soundness bar is unchanged: `mutex1` and `mutex2` must stay separate
identities, or the racing tasks get wrong answers instead of honest errors.

### Float literals were built one bit short — SHIPPED (a wrong-value bug, not a refusal)

`ExpressionVisitor`'s FP literal path built `new BigFloat(text, new BinaryMathContext(significand - 1,
exponent))` — 23 bits for `float`, 52 for `double` — and then stored the result in a full-width
`FpType(exponent, significand)`. MPFR's precision counts the significand **including** the implicit
leading bit (24 / 53), which is exactly what `FpUtils#bigFloatToFpLitExpr`, `FpType` and the core
test (`BinaryMathContext(24, 8)` for FLOAT) all use. So every literal was rounded one bit short.

Visible effect: `1 + 2^-23` is a tie at 23-bit precision and rounds to exactly `1.0f`, so a
program's own `1.0000001f > 1.0f` read as **false** and safe float programs were reported **Unsafe**.
Ground truth taken from gcc, not from my own FP reasoning: all the fixture's comparisons are true,
and `1.0000001f` has exactly the bits `0x1.000002p+0`.

**Pre-existing, but I propagated it.** The `- 1` was already there before `eab619083c` (hex float
constants); that commit copied the same context into the new hex branch. It also means the earlier
"hex floats unlocked 16 of 30" figure measured *parse success* while the values were subtly wrong.

**How it was found — the diagnosis path is worth keeping.** Two hypotheses died cheaply before the
real one:
1. "`float-rounding1` fails because theta ignores `fesetround`" — refuted by the **trace length of 3**:
   it failed on the *first* check, which uses the default rounding mode.
2. "my hex-float commit is wrong" — refuted by a **decimal control**, `1.0000001f > 1.0f`, failing
   identically.

**Measured.** Six probes wrong → correct. A 40-task sample across floats-cbmc-regression,
floats-esbmc-regression and float-benchs, run **both ways on the same tasks**: 15 correct / 1 wrong /
24 no-answer, *identical* before and after, no per-task change.

That flat result is deliberately not read as "no effect". Unlike the three fixes reverted this
session — which produced byte-identical *error signatures*, i.e. the code path never engaged — here
the mechanism provably fires on every float literal. For a global value change the sample's job is
**regression detection**, and it found none; whether other tasks flip is a question only a full run
answers. Shipped on the demonstrated wrong answer, with the fixture A/B'd (Safe with, Unsafe
without) — not on sample movement.

**Residue, now a queue item:** the sample's one wrong is `float-rounding1`, which after this fix
fails on its *second* check — `fesetround(0x400)` (FE_DOWNWARD). Theta models no dynamic rounding
mode and silently ignores `fesetround`, then answers confidently. By the batch's own rule that is
backwards: it should **refuse** a non-default `fesetround` (0 rather than −16). Small and principled.

### fesetround: refuse a rounding mode theta does not model — SHIPPED

theta models one rounding mode, round-to-nearest-even (the C default). `fesetround` was silently
ignored, so a program selecting FE_DOWNWARD carried on being evaluated to-nearest and answered
confidently wrong — `floats-cbmc-regression/float-rounding1` asserts a sum under downward rounding
and was reported Unsafe though it is safe. By the batch's own scoring rule that is backwards: an
honest refusal is 0, that wrong answer is −16.

Now: `fesetround(0)` (FE_TONEAREST) is a no-op returning 0; any other constant, **or a non-constant
argument**, is refused; `fegetround()` returns 0, which is sound precisely because anything that
would have changed the mode was refused. Measured: FE_DOWNWARD → refused, `fesetround(0)` → still
Safe, `float-rounding1` → refused instead of wrong `false` (**+16**). Fixtures both ways
(`fesetround_nondefault.c` FRONTEND-FAIL, `fesetround_default.c` SAFE).

### aws_linked_list_node_reset_harness — a FOURTH bucket on the byte-granular memory model

Reproduces locally: Unsafe, **trace 10**. The harness is

```c
memset(node, 0, sizeof(*node));                             /* cell-granular write */
__VERIFIER_assert(aws_is_mem_zeroed(node, sizeof(*node)));  /* reads byte-by-byte via uint8_t* */
```

`aws_is_mem_zeroed` walks the object as `const uint8_t *`. Under a cell-per-value model those byte
reads do not correspond to the cell writes `memset` made, so the check fails on a safe program.

**Four independent buckets now converge on the bytes model**: intel-tdx before-parsing (344 files),
float↔int union punning (~298), this aws family, and `float-to-double2`. None is reachable by local
patching. That is the clearest prioritisation signal this batch has produced.

`uthash_JEN_nondet_test2-2` and `ldv-memsafety/ArraysOfVariableLength` give **no answer even at 900 s
locally**, so they cannot be triaged on this host — they need the benchmark's hardware.

⚠️ **Process note:** one gate run reported `FAIL/ERROR: 0` from an *empty* file — the command ran
gradle from the repo root and then `./run_canaries.sh` from there, which does not exist
(`GATE_EXIT=127`). Only the exit code exposed it. Always check `GATE_EXIT` and the `Fixtures:` line,
never a bare FAIL count.

## Resource exhaustion — MEASURED, BUT EXPLICITLY NOT A TARGET (user decision, 2026-08-10)

⚠️ **Do not work on timeouts/OOM.** They are expected behaviour for this tool on these benchmarks.
The measurement below is kept as context — it explains why answered-rate is what it is, and it is a
design input for the bytes model (which would *add* cost) — but it is **not** a work item and must
not be proposed as one again.

**Priority order set by the user (2026-08-10):**
1. **Correctness / soundness — highest, and urgent once run 87 lands.** For each wrong answer:
   fix it if possible; if not, find exactly what is under-implemented and **throw there**, so the
   task fails loudly (0) instead of answering wrongly (−16/−32).
2. goblint-regression (pthread handles through pointer parameters).
3. intel-tdx-module.

## Context only: where run 86's non-answers sit

Measured over all 72,103 task-runs of run 86:

| bucket | runs | share |
|---|---|---|
| **TIMEOUT** | 26,816 | **37.2%** |
| answered (true / false / unknown) | 25,728 | 35.7% |
| **OUT OF MEMORY** | 13,249 | **18.4%** |
| ERROR (frontend, solver, other) | 6,310 | 8.8% |

**~40,000 runs — 55.6% — score 0 because the analysis runs out of time or memory.** Every frontend
error bucket *combined* is 6,310, and the ones triaged in detail this batch are far smaller than
that: intel-tdx before-parsing 344 files, goblint 507 runs, the whole bitfield-store family 407.

This does not invalidate the frontend work — wrong answers cost −16/−32 and fixing them is worth
more per task than a timeout is — but it does say the **largest remaining pool of points is
resource-bound, not correctness-bound**, and that no amount of grammar or modelling work touches it.
A timeout and an OOM both score 0, exactly like an error, so converting even a few percent of 40,000
runs outweighs closing any single frontend bucket.

Worth noting alongside the byte-granular finding: the bytes model would *add* cost to an analysis
already losing over half its runs to cost. Both facts should inform that project's design, not just
its priority.

Concrete resource-side items already on the list (PLAN.md "Cleanups"): drop
`allocateArrayElements`' redundant per-element subobjects (the `outerarr` slowness), and fold
literal div/mod in `SimplifyExprsPass`. Neither has been measured for effect yet.

### Housekeeping from the 2026-08-10 pass

**Both "Cleanups" items are stale — removed from the queue, not reimplemented.**
- *Fold literal div/mod in SimplifyExprsPass*: core's `ExprSimplifier` already folds literal
  `IntDivExpr`, `IntModExpr` **and** `IntRemExpr` (lines ~885–940). The pass delegates to
  `ExprUtils.simplify`, so there is nothing to add. (Where an unfolded `(mod 4 4294967296)` shows up,
  as `CLibraryFunctionsPass` documents, the cause is simplify not being *applied* at that point, not
  a missing rule.)
- *`allocateArrayElements` redundant per-element subobjects*: already guarded —
  `if (aggregateFields.isEmpty()) return`, added in `575da57eae`, with the comment "the whole array
  costs zero allocations however long it is".

**Float-precision regression check, on the right population this time.** The 40-task sample used to
clear `2a7e482564` drew from floats-cbmc-regression / floats-esbmc-regression / float-benchs — but
the family most exposed to a change in every float literal is `hardness` (float-heavy, 15% of the
benchmark, 11,546 resource-bound runs). Re-checked against 10 `hardness` tasks that answered `true`
in run 86: **10/10 still correct**, all within the local limit. No regression.

**`scopes4-1` (scopes cause B1) reproduced, hypothesis killed.** Unsafe (valid-deref) at 500 s
locally, **trace length 1152**, and **zero** "Variable already exists" warnings.

The tempting hypothesis was a static-local name collision: `foo2` has `static int arr[1024]`
(written at index 194) and `foo` has `static int arr[123]`, so collapsing them would make `arr[194]`
look out of bounds. It is wrong twice over — `promoteStaticLocal` registers into each function's own
scope via `variables.peek()`, so the two never meet, and the run emits no collision warning at all.
Checked before building on it.

The long trace also puts this *outside* the class the trace-length heuristic identifies: the
false-alarm bugs fixed this session had 6–7 step counterexamples, while 1152 steps on a 17-line
program suggests the analysis is walking the 1024-element static array itself. Next step is
instrumentation of where the deref bound check fails, not another hypothesis.

### scopes4-1 (cause B1): reproduced, but not bisectable by simplification

State with **all 7 of this session's fixes**: `Unsafe (valid-deref)`, **trace 1152**, expected `true`.
A genuine wrong `false` — the highest-priority class.

Two hypotheses already killed:
- *static-local name collision* (`foo2` has `static int arr[1024]`, `foo` has `static int arr[123]`):
  `promoteStaticLocal` registers into each function's **own** scope via `variables.peek()`, and the
  run emits **zero** "Variable already exists" warnings.
- *the trace-length heuristic doesn't apply here*: 1152 steps is nothing like the 6–7 step
  counterexamples of the false-alarm bugs fixed this session. It most likely reflects walking the
  1024-element static array.

⚠️ **Simplified variants cannot be used to bisect it.** Cut-down versions
(`static int arr[16]; arr[3]=13; return arr+1;` etc.) do not answer at all — the portfolio picks a
BOUNDED/`KIND-Z3` config on them and the checker subprocess dies with
`ErrorCodeException(2147483646)`. Not memory: it reproduces at `-Xmx2g` as well as `-Xmx4g`, and a
control file passes on the same dist. That is a separate defect (an ERROR, score 0, so lower
priority than the wrong answer), but it means **bisection by simplification is unavailable** for this
task — the next step must be instrumenting `MemsafetyPass`'s deref bound check on the real file.

⚠️ **Local-run trap worth remembering:** building the archive for a benchmark upload does
`rm -rf …/Theta-svcomp` and only produces the zip. Local runs then fail with
`NoSuchFileException: …/Theta-svcomp/solvers` — which looks like "no answer" if only the verdict is
parsed. Four bisect runs were scored as no-answer before this was spotted. **Re-extract the zip
after building it for upload.**

### no-overflow additive chains: minimal repro found, and the cause is NOT the frontend

All three tasks confirmed as **wrong `true` (−32 each)** with all seven of this session's fixes in
place: `Stockholm-2`, `dijkstra6-both-nt` (both expect `false`), and a **4-line repro**:

```c
extern int __VERIFIER_nondet_int(void);
int main(){ int x=__VERIFIER_nondet_int(), a=__VERIFIER_nondet_int(), b=__VERIFIER_nondet_int();
  if (a == b) { while (x >= 0) { x = x + a - b - 1; } } return 0; }   /* answers Safe; is not */
```

The overflow is the **intermediate** `x + a` (take `x = a = b = INT_MAX`); with `a == b` the whole
chain is worth `x - 1`, so the value is in range while a sub-expression is not.

**Narrowed by variants — it needs the guard AND the chain together:**

| variant | verdict |
|---|---|
| straight-line `int y = x + a - b - 1;` under `if (a==b)` | Unsafe ✓ |
| loop, full chain, **no** `a==b` guard | Unsafe ✓ |
| loop, `x = x + a`, with guard | Unsafe ✓ |
| loop, `x = x + a`, no guard | Unsafe ✓ |
| **loop + guard + full chain** | **Safe ✗** |

**Two hypotheses tested and killed:**
1. *"intermediates are not checked"* — a straight-line version of the same chain is correctly
   Unsafe, as is a bare `x + a`.
2. *"`SimplifyExprsPass` collapses `x+a-b-1` to `x-1` before the checks are inserted"* — plausible
   because `OverflowDetectionPass` sits at `ProcedurePassManager` line 130, *after* SimplifyExprs
   (68/98/126), LoopUnroll (69) and Lbe (111/123). **Refuted by tracing:** SimplifyExprs correctly
   skips while `verifiedProperty == OVERFLOW`, the overflow pass then inserts its checks (6 edges in
   the failing case vs 4 in the passing one), and simplification only runs afterwards, when the
   checks are already explicit error edges.

**So the checks are emitted and the wrong answer comes from downstream — the analysis proves the
error edge unreachable when it is not.** That makes this an abstraction/CEGAR soundness issue, not a
frontend one, and it is the most expensive class in the batch (−32). Next step: run the 4-line repro
under the individual portfolio configurations to find which one returns Safe, rather than through
`--portfolio STABLE`, then look at that config's abstraction.

#### ROOT CAUSE: additive chains are flattened to n-ary Add, so C's intermediates cannot be checked

Traced `OverflowDetectionPass`'s candidate expressions on the failing and passing repros. **Both
produce exactly the same arithmetic**:

```
TRACE arith exprs=3 withCType=1 :: (- main::b) | (- 1) | (+ main::x main::a (- main::b) (- 1))
```

`x + a - b - 1` is **one flattened n-ary `AddExpr`**. C evaluates it left to right as
`((x + a) - b) - 1`, and it is the *intermediate* `x + a` that overflows — but that sub-expression
does not exist in the IR, so the pass can only range-check the **final sum**. Everything follows:

| case | final sum | verdict |
|---|---|---|
| loop, no `a==b` | `x+a-b-1`, unconstrained → can overflow | Unsafe ✓ |
| straight-line, `a==b` | `x-1`, `x` unconstrained → `INT_MIN-1` underflows | Unsafe ✓ (a *different*, real overflow) |
| **loop + `a==b`** | `x-1` with `x >= 0` → always in range | **Safe ✗** (misses `x+a`) |

**Two earlier conclusions were wrong and are corrected here:**
1. *"`SimplifyExprsPass` erases the chain before the checks"* — refuted by tracing: it correctly
   skips while `verifiedProperty == OVERFLOW`.
2. *"`PRED_CART` is unsound"* — it returns Safe, but so does **BMC** on the same model. Both are
   correctly proving a model that has no reachable overflow edge. The defect is the model, not the
   abstraction. (Filing an unsound-abstraction bug here would have been wrong.)

**Fix directions**, in preference order:
1. In `OverflowDetectionPass`, expand an n-ary additive chain into its **binary prefixes**
   (`x+a`, `(x+a)-b`, …) and range-check each. Purely local to the pass; no IR change; the operand
   order in the flattened node is the C evaluation order, so the prefixes are recoverable.
2. Stop flattening additive chains in the frontend when the property is no-overflow — bigger blast
   radius, and it would pessimise every other property.

⚠️ Note the second filter condition: candidates must carry **`cType` metadata**, and only 1 of the 3
expressions above has it. `FrontendMetadata` is identity-keyed, the same trap that defeated the
bitfield store, so any prefix synthesised in fix 1 must be given its `cType` explicitly or it will
be silently filtered out.

#### FIX SHIPPED: range-check the intermediates of a flattened chain

`OverflowDetectionPass` now expands an n-ary `AddExpr`/`MulExpr` into the intermediates C actually
computes (`x+a`, then `(x+a)-b`, …) and range-checks each, instead of only the final value. Operands
are already in evaluation order, so each proper prefix is exactly one intermediate; the full-length
one is skipped because the original node is already checked.

⚠️ Every synthesised prefix is stamped with the chain's own `cType`. The candidate filter requires
that metadata and `FrontendMetadata` is **identity-keyed**, so a freshly built expression carries
none and would be silently filtered out — the fix would have been a no-op. Same trap that defeated
the bitfield store's first two designs.

**Measured both directions:**

| | before | after |
|---|---|---|
| loop + `a==b` + full chain (the `Stockholm-2` shape) | Safe ✗ | **Unsafe ✓** |
| loop, no guard / simple body (3 controls) | Unsafe | Unsafe ✓ |
| **14 no-overflow tasks that expect `true` and answered `true` in run 86** | true | **12 Safe, 2 timeout, 0 false alarms** |

That last row is the one that mattered: the change adds checks to *every* additive and
multiplicative chain in the benchmark, and is sound only because the flattened operand order is C's
evaluation order. Had anything reordered operands (a normaliser doing so on commutativity would be
natural), the prefixes would be wrong intermediates and safe programs would report `false` at −16
each. Sampling the exposed population found none.

Fixture `overflow_chain_intermediate.c` (UNSAFE:no-overflow). Its A/B is real but asymmetric in
time: with the fix it answers Unsafe in <200 s; without it the identical program does not answer at
200 s and answered `Safe` at 900 s.

**Confirmed on the real tasks at the full 900 s budget:**

| task | before | after | expected |
|---|---|---|---|
| `termination-crafted/Stockholm-2` | `true` (−32) | **`false`** ✓ | false |
| `termination-nla/dijkstra6-both-nt` | `true` (−32) | **`false`** ✓ | false |
| `termination-crafted/Stockholm-1` (control) | `true` ✓ | `true` ✓ | true |

A **+66 swing** on these two alone (−32 each → +1 each), with the safe control unchanged and no
false alarms in the 14-task sample. The `no-overflow additive chains` item is closed.

### scopes cause G (`scopes1`): address-taken scalars are never released — design verified, not yet implemented

`scopes1` expects **false** and answers **`true`** (−32, the expensive class). It is a plain
use-after-scope on a *scalar*:

```c
int *pA = 0;
{ int a = 7; pA = &a; }        /* a's storage dies here */
int b = 3; int *pB = &b;
int sum = *pA + *pB;           /* use-after-scope; must be reported */
```

The rest of the family is already correct (`scopes2/3/4-2/5` all answer `false(valid-deref)`), so the
scope-release machinery works — it just never covers this case.

**Why.** `registerScoped` has exactly **one** caller (`FunctionVisitor` line 1377), the *alloca*
path for block-local arrays. An address-taken **scalar** never goes through it: `ReferenceElimination`
gives it a compile-time `3k+2` base at procedure entry instead, so no `__theta_scope_end` marker is
emitted and `__theta_ptr_size[base]` is never cleared. The deref after the block is then accepted.

**The lowering already exists and would work unchanged.** `AllocaFunctionPass#lowerScopeEnds` turns
`InvokeLabel(SCOPE_END, params)` into `deallocate(parseContext, params[1])`, gated on
`MemsafetyPass.enabled`. So the whole fix is on the emitting side.

**Design:**
1. In `ExpressionVisitor`'s `&` case, tell the function visitor which `VarDecl` had its address
   taken.
2. In `FunctionVisitor`, register that decl with the *current* scope, exactly as `registerScoped`
   does for allocas — but **only** when it is block-local and **not** `static` (a static local
   outlives the block and must never be released; parameters are fine, their block is the body).
3. At scope end (`withScopeReleases`), emit `SCOPE_END` for it.

⚠️ **The one refactor this needs:** `scopedAllocas` currently holds `VarDecl<?>`, and the marker's
`params[1]` is the *variable's ref*, which for an alloca'd array already holds the base. A scalar's
variable holds its **value**, not a base — the thing to release is `&var` (a `Reference` expr, which
`ReferenceElimination` later folds to the `3k+2` literal). So the scope list has to carry the
*expression to release* rather than the decl. That touches `scopedAllocas`, `registerScoped`,
`releaseScopedInto` and `scopeMark`.

Everything above is verified against the code, not assumed; only the refactor remains. Keep the
memsafety gate: no other property's XCFA should change.

#### FIX SHIPPED: address-taken scalars are released at the end of their own block

`memsafety-ext3/scopes1` answered **`true`** against an expected `false` — a use-after-scope missed
outright (−32). The rest of the family (`scopes2/3/4-2/5`) was already correct, so the machinery
worked; it simply never covered scalars.

The refactor the design called for is done: the scope stack now holds the **release expression**
instead of the `VarDecl`. An alloca'd array's variable already *holds* its base, so releasing
`varDecl.getRef()` was right for it; a scalar's variable holds its **value**, and the thing to
release is `&a` (a `Reference`, which `ReferenceElimination` folds to the `3k+2` base).

**Three ways this could have broken programs that already worked, and how each is handled:**
- *releasing too early* — registration walks the scope stack to the block that **declared** the
  variable, not the one where `&` appears, so `{ p = &a; }` inside `a`'s block does not end `a`'s
  life at the inner brace;
- *double release* — a per-scope `Set<VarDecl>` dedups, so `&a` twice releases once (a second
  release would read as a double free);
- *objects that outlive every block* — static locals are skipped via `staticLocals`, and the
  outermost scope (globals) is skipped outright.

**Measured:**

| case | before | after |
|---|---|---|
| `scopes1` | `true` (−32) | **`false`** ✓ |
| `&a` in a nested block, `a` declared outside | Safe | Safe ✓ |
| address taken twice | Safe | Safe ✓ |
| static local's address | Safe | Safe ✓ |
| global's address | Safe | Safe ✓ |

Gate: 60/60 fixtures — including every pre-existing alloca/scope fixture
(`scope_end_release`, `scope_end_loop_iteration`, `scope_lifetime_ok`, `alloca_use_after_return`,
`alloca_lifetime_ok`), which are exactly the previously-supported behaviour this refactor put at
risk. New fixture `scope_end_scalar.c` covers the scalar direction and all three regression shapes.

Still open in this family: **`scopes4-1`** (cause B1) — expects `true`, answers `false(valid-deref)`,
trace 1152, and is **not bisectable by simplification** (cut-down variants crash the bounded
backend; see above).

## Batch 87 RESULTS — measuring this session's fixes (finished 2026-08-11 19:16 CEST)

`results-run87/`, IDLE on benchcloud, `theta27-long900.xml`, Skylake-pinned — same host/XML/CPU as
runs 80 and 86. Tool dir = `db8aecc4a1`, i.e. it measures: GCC builtins, struct-cache invalidation,
typedef'd array extents, ternary short-circuit, multi-cell bitfield store, **float-literal
precision**, and the `fesetround` refusal. (The later overflow-chain and scope-scalar fixes are
**not** in it.)

| | run 86 | run 87 | delta |
|---|---|---|---|
| SV-COMP score | 19,516 | **19,705** | **+189** |
| correct | 12,815 | 12,825 | +10 |
| **wrong** | **65** | **55** | **−10** |
| wrong true (−32) | 20 | 19 | −1 |
| wrong false (−16) | 45 | 36 | −9 |
| error | 23,314 | 23,313 | −1 |

vs run 80 the arc is now 13,828 → 19,705 (**+5,877**) and wrong 393 → 55.

### ⚠️ One regression, and it is mine: `floats-cbmc-regression/float-no-simp7`

`true` → `false(unreach-call)`; expected `true`. Caused by the float-literal precision fix
(`2a7e482564`) — the only change that moves float values.

```c
float f = 0x1.9e0c22p-101f, g = -0x1.3c9014p-50f, target = -0x1p-149f;
if (!(f * g == target)) reach_error();     /* gcc: the equality HOLDS */
```

gcc confirms the program is safe and that the literals are exactly as written — `0x1.9e0c22` needs a
full 24-bit significand, which is precisely the bit the fix restored. So **theta used to have wrong
literals and get the right answer; it now has right literals and gets a wrong one.** The exposed
defect is in **subnormal (gradual-underflow) rounding**: `-101 + -50 = -151`, so the product lands
below the smallest normal and near the tie between `0` and `2^-149`, where the old one-bit literal
error happened to compensate.

Probed and ruled out: it is **not** flush-to-zero — the subnormal literal is non-zero, the subnormal
product is non-zero, and a normal-range control is fine. theta simply computes a different subnormal.

**Do not revert the precision fix over this.** It is gcc-verified, it corrects *every* float and
double literal in the benchmark, and run 87 is +189 with wrong down 10 overall; this single task is
−16 against that. The right follow-up is the subnormal rounding path itself.

Also newly wrong from a non-answer: `heap-manipulation/bubble_sort_linux-1` (TIMEOUT → `false`),
which is a task that merely started answering, not a regression.

### Run 87 wrong-set triage (authoritative benchexec categories)

⚠️ **Count correction.** A YAML-derived script of mine reported 188 wrong task-runs; that was wrong —
it misclassified `combinations` (88 entries, all actually correct). benchexec's own `category`
column gives **102 wrong runs** across all 72,103, ≈51 distinct tasks (each appears twice).
`compare_runs.py`'s 55 is the same data restricted to the 36,531-run common subset. **Use the
`category` column, not re-derived expectations.**

| wrong runs | family | verdict given |
|---|---|---|
| **26** | **termination-15** | `false(valid-deref)` ← largest group, −16 each |
| 8 + 6 | aws-c-common | `false(unreach-call)` / `true` |
| 6 | pthread-race-challenges | **`true`** (missed race, −32) |
| 6 | ldv-memsafety | `false(valid-deref)` |
| 4 | memory-model (`2SB`, `4SB`) | **`true`** (−32) |
| 4 each | floats-cbmc-regression, uthash-2.0.2, list-ext-properties, memsafety | mixed |
| 3 | goblint-regression | **`true`** (−32) |
| 2 each | libvsync, termination-crafted, termination-nla, ldv-regression, heap-manipulation, ldv-linux-4.0-rc1-mav, termination-memory-alloca | mixed |

(`termination-crafted`/`termination-nla` = Stockholm-2 + dijkstra6-both-nt, already fixed after this
run's archive was built; likewise `memsafety-ext3/scopes1`.)

**Next target: `termination-15`, 13 distinct tasks, all `*_reverse_alloca` / `*_mixed_alloca`.**
A backwards buffer walk:

```c
char *s = alloca(length);  s[0] = '\0';  s += length - 1;
while (*s != '\0' && *s != c) s--;        /* stops at index 0, which holds '\0' */
```

Expected `true`; theta reports `false(valid-deref)`. Safety depends on the invariant `s >= base`,
held because index 0 carries the terminator. Distinct from the already-fixed alloca-string cases
(`openbsd_cstrncmp-alloca-*`, handled by `NarrowCellRangePass`) and from the `pointer_backwards_walk`
fixture, which only pinned that `p--` keeps its sign. Classification (modelling bug vs precision)
pending on trace length.

#### ROOT CAUSE (termination-15, 13 tasks): a mid-object pointer loses its bounds when passed to a function

Classified by trace length first: `cstrchr_reverse_alloca` fails at **trace 6**, `cstrcmp_mixed_alloca`
at **trace 9** — far too short for loop-invariant reasoning, so a modelling bug, not precision.

**Minimal repro (9 lines, trace 6), and the backwards walk is NOT needed:**

```c
char peek(const char *s){ return *s; }
int main(){ int n = __VERIFIER_nondet_int(); if (n < 1) n = 1;
  char *p = (char*) alloca(n * sizeof(char));
  p[0] = '\0';
  p += n - 1;                       /* mid-object pointer, still in bounds */
  if (peek(p) == 'x') reach_error();/* Unsafe -- FALSE ALARM */ }
```

**Bisected:**

| variant | verdict |
|---|---|
| `alloca(n*sizeof(char))`, `p += n-1`, read `*p` **in main** | Safe ✓ |
| `alloca(n)`, `p += n-1`, read in main | Safe ✓ |
| `alloca(10)`, `p += 9`, read in main (constant size) | Safe ✓ |
| **same, but the pointer is passed to a function and read there** | **Unsafe ✗** |
| same, with the backwards-walk loop in the callee | Unsafe ✗ (identical trace 6) |

So it is neither the symbolic size, nor the pointer arithmetic, nor the loop: **a pointer of the form
`base + offset` loses its bounds across a call**, and the first dereference in the callee is reported
invalid. The parameter assignment is a *store* of a split pointer — the same shape cause D refuses
outright (`UnsupportedPointerSplitException`, fixture `store_split_pointer.c`) — but here it does not
refuse, it silently drops the offset (or base) and the check then fails. A silent wrong answer where
the sibling path takes a loud refusal.

Worth **−416** as a class (26 wrong runs, 13 tasks) and the largest group in run 87. Next step: trace
what the callee's parameter holds — base only, offset lost, or a base that is no longer the object's
— rather than guessing which of the three it is.

## Re-evaluation of every reverted/parked fix (user direction, 2026-08-11)

⚠️ **Criterion changed: keep a fix if it is genuinely correct, regardless of its point effect.**
Turning an error into a timeout/OOM, or uncovering a further bug, counts as progress. A correct
parsing/modelling fix that exposes a latent defect elsewhere stays in — the latent defect is then the
next thing to debug, not a reason to revert.

| item | verdict | why |
|---|---|---|
| **dimensionless arrays** (`stash@{0}`) | **RESTORED** | valid C, and it removes a real asymmetry — the *global* path already infers the extent from the initializer (`FrontendXcfaBuilder#getArraySize`); only the local path did not. Parked before only because it measured net −32. |
| **whole-cell address-of** | **RESTORED** | `&` on a full-width `extract` does name storage, so refusing it as "not an lvalue" was simply wrong. |
| `sliceCarrier` (bitfield metadata peeling) | stays out | **not a fix at all**: tracing proved `BitfieldSlice.CELL` is absent on the lvalue *and every ancestor*, so the peeling can never find anything. Inert code. |
| structural single-cell bitfield match | already shipped | subsumed by the multi-cell store (`if (unit is Dereference) …`). |

**Measured effects (both are "progress without points", exactly as intended):**

- *dimensionless arrays*, on its 10-file bucket: all 10 now get past the NPE — 1 succeeds outright,
  1 reaches the `fesetround` refusal, and **8 expose a new bug**.
- *whole-cell address-of*, on the intel-tdx before-parsing sample: **3 files** move from an internal
  `IllegalStateException: Referencing non-lvalue expressions is not allowed!` to the documented
  byte-union multi-cell refusal. They still do not verify (that needs the bytes model), but a
  limitation-crash became an honest, documented failure.

### NEW BUG uncovered by the dimensionless-array restore

`ProcedureInliningKt.inlineCallSite(ProcedureInlining.kt:192)` —
`IndexOutOfBoundsException: Index 2 out of bounds for length 2`, on 8 of the 10 files
(`ddv-machzwd/ddv_machzwd_*`). An argument/parameter count mismatch while inlining a call: the call
site supplies more arguments than the callee has parameters (or the reverse). Previously hidden
behind the NPE. Worth handling properly — at minimum it should refuse with a message naming the
callee and both arities, instead of an `IndexOutOfBoundsException`.

**Also corrected:** the earlier justification for keeping the float-literal precision fix leaned on
net points. The right justification is that the fix is gcc-verified correct and the subnormal-rounding
defect it exposed is a real bug that had to be found regardless.

### Inlining arity mismatch: crash → named refusal, and the mismatch is OURS

`ProcedureInlining.kt:192` indexes `invokeLabel.params[i]` by the *callee's* parameter position, so
any arity disagreement walks off the end. 8 `ddv-machzwd` files died with a bare
`IndexOutOfBoundsException: Index 2 out of bounds for length 2` — naming neither the procedure nor
the counts. (Uncovered by restoring the dimensionless-array fix, which let those files get this far.)

⚠️ **My first guard blamed the input, and that was wrong.** Its message said "a call through a
declaration whose parameter list disagrees with the definition". The source says otherwise:

```c
void outb(unsigned char byte, unsigned int);   /* declared with 2 params, never defined */
outb(0x12, 0x218);                             /* every call passes 2 */
```

Yet the callee arrives with **3** parameters. The disagreement is **internal** — an only-declared
`void` function gains a synthetic return slot that its call sites do not supply. Shipping the first
message would have pinned theta's own defect on the benchmark.

The refusal now reports both counts and says explicitly that it is an internal disagreement, "not
necessarily a fault in the input". 8 files move from an opaque crash to a named refusal: same score,
but actionable.

**The real fix is upstream and still open:** either the stub built for an only-declared `void`
function should not carry a return slot, or its call sites should pass one. Confirm which side is
wrong before changing either.

⚠️ **Tooling trap (second variant).** A gate run was reported as *failed, exit 1* while being fully
green: the command chain ended in `grep -c "^(FAIL|ERROR)"`, and grep exits 1 when it matches
nothing. The earlier variant was the mirror image — a *false green* from grepping an empty file after
`run_canaries.sh` was invoked from the wrong directory. **Read the `Fixtures:`/`RESULT:` lines; never
trust the pipeline's exit status alone.**

## Exploratory per-config runs (batch 88) — 6 of 10 in

Each config run **standalone** (not through the portfolio), 5 min / 7 GB / 2 cores, IDLE,
Skylake-pinned, HEAD build `7976b40d75` = `Theta-svcomp-88`. Subsets chosen per config rather than
running everything everywhere: the general backends on 11 sequential unreach-call groups, MDD on the
control-heavy three (ECA / ControlFlow / ProductLines), OC on Concurrency only, LIVENESS_CEGAR on
termination only.

| config | runs | correct | % | wrong | timeout | oom | stuck | srv-err |
|---|---|---|---|---|---|---|---|---|
| CEGAR EXPL/NWT_IT_WP | 11,412 | 2,046 | **17.9%** | 10 | 2,374 | 2,366 | 1,832 | 1,792 |
| KIND | 11,412 | 1,522 | 13.3% | 10 | 5,504 | 2,120 | 0 | 0 |
| BMC | 11,412 | 1,446 | 12.7% | 10 | 5,846 | 2,136 | 0 | 0 |
| IMC | 11,412 | 928 | 8.1% | 8 | 4,184 | 3,396 | 0 | 98 |
| **MDD** | 3,870 | **0** | **0.0%** | 4 | 412 | 1,274 | **2,064** | 0 |
| OC | 1,030 | 561 | **54.5%** | 3 | 184 | 19 | 0 | 32 |

### Findings

**1. Standalone MDD solves nothing on the sets picked to suit it.** 0 correct in 3,870 runs; its
only 4 answers were `true` and *all four were wrong*. 53% end as "verification stuck" (exit 220),
33% OOM, 11% timeout. Caveat before acting: this is `--backend MDD` alone at 5 min — the portfolio
may give it different settings or budget — but on ECA/ControlFlow/ProductLines it contributed
nothing here and was actively harmful the few times it answered.

**2. OC is far and away the most productive per task** (54.5% correct) on Concurrency, its home
ground, and barely uses memory (19 OOM in 1,030). Its main loss is **223 `frontend failed, after
parsing`** — a fifth of the concurrency set never reaches the checker, which is a frontend problem,
not an OC one.

**3. "verification stuck" and "server error" are not resource exhaustion** and are worth separating
from the timeout/OOM pool that is off the work list. They concentrate in exactly two configs:
EXPL (1,832 stuck + 1,792 server errors) and MDD (2,064 stuck). BMC/KIND have **zero** of both —
they fail cleanly by timeout instead. Whatever "stuck" and "server error" are, they are specific to
those two analyses rather than general.

**4. Nothing here beats the portfolio**, as expected — EXPL alone tops out at 17.9% of the sequential
set at 5 min. The value of these runs is the per-config profile, not the totals.

Still running: `predcart`, `predcart_bv` (identical task set to `predcart`, `--arithmetic bitvector`
— a controlled encoding comparison), `ic3`, `liveness`.

### Bitvector encoding: `bit2bool` back-transformation — SHIPPED, and the real story is the solver

The batch-88 exploratory run gave `predcart_bv` (PRED_CART/BW_BIN_ITP + `--arithmetic bitvector`)
**2,946 server errors** across **1,473 distinct tasks** in a dozen unrelated families
(product-lines 532, neural-networks 354, seq-mthreaded 530, nla-digbench 250, array-* 400+ …). Every
one reproduces as:

```
java.lang.NullPointerException: Unsupported function 'bit2bool' in Z3 back-transformation.
```

Z3 emits `(_ bit2bool k) x` when reasoning about individual bits; theta's `(name, arity)` dispatch
had no entry, so it fell through to `toFuncLitExpr`, which requires a model and NPE'd without one.
Handler added to **both** Z3 transformers (current + legacy), reading the index from the term text
the way the neighbouring `extract` case does, lowering to `extract(op, k, k+1) == 1`.

⚠️ **I had seen this error and dismissed it.** It appeared during the pre-submission smoke test on
`bitvector/byte_add-1.c` and I called it "task-specific, like OC's calloc". It was the single
largest failure mode of the encoding I was about to submit. The per-config split is what exposed the
scale — a portfolio run would have hidden it behind a fallback.

**Correctness established, not assumed.** The fix's only effect on real tasks is crash → *timeout*,
which proves nothing about the lowering, so three bit-level probes were run to a verdict:

| probe | expected | got |
|---|---|---|
| `(x&1)==1` then `(x&1)==0` | Safe | Safe ✓ |
| bit 3 set, `8 <= x < 16` | **Unsafe** | Unsafe ✓ |
| `y = x \| 1` vs an even constant | Safe | Safe ✓ |

The UNSAFE case is what makes the set discriminating: an inverted comparison or off-by-one index
cannot pass all three. Fixture `bitvector_bit2bool.c`.

**Limits, stated plainly:**
- Worth **no points**: sampled tasks go from server error to timeout, not to answers.
- **Not the only 202 cause** — `neural-networks/log_4_safe` still server-errors, so at least one more
  back-transformation gap sits behind that 2,946.
- **Z3-path only.** MathSAT has its own transformer and never touches this code.

### The bitvector collapse is a SOLVER limitation, not the encoding

Behind the `bit2bool` crash sits `Z3Exception: theory not supported by interpolation` (exit 221):
legacy Z3 cannot interpolate over bitvectors, which `BW_BIN_ITP` requires. Same domain, refinement
and encoding under **MathSAT 5.6.12** instead:

| task | Z3 + bitvector | MathSAT + bitvector |
|---|---|---|
| `bitvector/byte_add-1` (expects **false**) | solver error 221 | **Unsafe = false, CORRECT** |
| `bitvector-loops/overflow_1-2` | solver error 221 | timeout |
| `loop-acceleration/array_1-1` | server error → timeout | timeout |

Zero solver errors under MathSAT. So `predcart_bv`'s 1,389 → 700 collapse is **not** the encoding
being unviable — it is the wrong solver for that refinement. A `predcart_bv_ms` run (identical task
set, MathSAT) is in flight to quantify it; the three runs form a chain with one variable each step:
efficient/Z3 → bitvector/Z3 → bitvector/MathSAT.

#### The other exit-202 cause: unmodelled math functions, misreported as "server error"

With `bit2bool` fixed, the remaining server errors in the bitvector sample resolve to:

```
java.lang.IllegalStateException: No such method logf.
   at XcfaAnalysisKt#getCoreXcfaLts$lambda$0:142
```

`neural-networks/*` call `logf` (and siblings). `FpFunctionsToExprsPass` models a good set of math
functions — `sqrt`, `fabs`, `floor`, `ceil`, `round`, `trunc`, `fmin/fmax`, `fmod`, the `is*`
classifiers — but **not** `logf`/`log`/`exp*`/`pow*`/trig. A call to one reaches the analysis as an
`InvokeLabel` naming a procedure that does not exist, and dies deep in the LTS with a bare
`IllegalStateException` that the tool-info maps to **exit 202, "server error"**.

That label is actively misleading: nothing about the server is wrong. It is an unsupported library
function, and it should say so — the same treatment given to the inlining arity mismatch
(`7976b40d75`): name the function, classify it as unsupported (exit 209/210), and let the score be
an honest 0 instead of an infrastructure-looking failure that invites the wrong investigation.

Two possible follow-ups, in order:
1. **Refuse clearly** where the missing procedure is detected — cheap, and stops mislabelling.
2. **Model the missing functions** where sound (`log`, `exp`, `pow` have no exact bitvector/integer
   semantics, so they would need an uninterpreted-function treatment with the usual caveats, not a
   made-up value).

⚠️ Do NOT invent values for these. An unsound `logf` would turn a 0 into a possible −16/−32.

## ROOT CAUSE: subnormal float literals are encoded as normals (core FP bug)

Chased from the run-87 regression `floats-cbmc-regression/float-no-simp7` and the bitvector-unique
wrongs (9 of 10 of which are float tasks). **Encoding-independent** — `--arithmetic efficient` and
`--arithmetic bitvector` are both wrong, `integer` honestly refuses floats:

| probe | expected | got |
|---|---|---|
| `2^-149 != 2^-126` | Safe | Safe ✓ |
| `2^-149 != 2^-148` | Safe | Safe ✓ |
| `2^-149 > 0` | Safe | Safe ✓ |
| `2^-100 < 2^-50` (normals, control) | Safe | Safe ✓ |
| **`2^-149 < 2^-126`** | Safe | **Unsafe ✗** |
| **`2^-149 > 2^-126`** | Unsafe | **Safe ✗** |

So subnormals are *distinct* and *positive*, and normal-range ordering is fine — but a subnormal is
placed **above** the smallest normal. They are being encoded too large.

**Mechanism — CORRECTED.** My first write-up above blamed the ENCODE side
(`bigFloatToFpLitExpr`) and sketched a fix for it. **That was wrong**, and the sketch would have
broken working code. Instrumenting MPFR directly (`scratchpad/FpProbe.java`) shows the encoder is
already correct: `0x1p-149` encodes to biased exponent **0**, significand 1 — bit-identical to
`Float.floatToRawIntBits`. MPFR's `exponent(minExp,maxExp)` returns `minExp-1` for subnormals
(the `Math.getExponent` convention), so the `+maxExponent` bias lands on 0 by itself.

The bug is the **DECODE**, `FpUtils.fpLitExprToBigFloat`:

```java
final var exponent = neutralBvLitExprToBigInteger(expr.getExponent())
                        .subtract(BigInteger.valueOf(maxExponent));          // 0 - 127 = -127
final var significand = neutralBvLitExprToBigInteger(expr.getSignificand())
                        .add(BigInteger.TWO.pow(type.getSignificand() - 1)); // ALWAYS +2^23
```

Both halves are wrong for a subnormal, and they compound:
- the implicit leading 1 is added unconditionally, but subnormals do not have one;
- exponent field 0 means `1 - maxExponent` (−126), not the `-maxExponent` (−127) it reads as.

Round-tripping through theta (`scratchpad/FpRt.java`) before the fix:

| literal | true value | theta decoded |
|---|---|---|
| `0x1p-149` | 1.4e-45 | **1.17549449e-38** |
| `0x1p-127` | 5.88e-39 | **1.76324153e-38** |
| `0x1p-126` | 1.1754944e-38 | 1.17549435e-38 ✓ |

Every subnormal came back as ≈`2^-126*(1+f)` — i.e. just ABOVE the smallest normal, which is
exactly the observed `2^-149 > 2^-126` = Safe. Doubles are hit identically: `Double.MIN_VALUE`
(4.9e-324) decoded as 2.225e-308, i.e. `DBL_MIN`.

**FIXED** — decode keys off a zero exponent field: no hidden bit, exponent `1 - maxExponent`. The
existing `BinaryMathContext(p, e)` represents the result exactly; no context widening was needed.
Since `fpLitExprToBigFloat` backs every comparison, add/sub/mul/div, rem, sqrt, min/max and
round-to-integral on `FpLitExpr`, this corrects subnormal handling across all FP folding, not just
literals.

Gated: `FpSubnormalTest` (new, JVM `Float`/`Double` as an independent oracle) + fixture
`float_subnormal_order.c`. **A/B verified** — with the fix reverted all 4 tests fail with exactly the
values above and `2^-149 < 2^-126` evaluates to `false`; 679 core tests pass with it.

⚠️ Remaining, NOT fixed: MPFR has no gradual underflow, so *arithmetic* that underflows below
`2^-149` yields a smaller BigFloat instead of flushing to zero, and only the re-encode rounds it.
That is a precision gap on the arithmetic path, not the ordering soundness bug fixed here.
Related: the significand off-by-one fix `2a7e482564`, which made literals exact enough for this to
become visible.

## Batch 89 — integer vs bitvector encoding, full suite (user request 2026-08-12)

Four full-suite runs at 5 min / 7 GB, Skylake-pinned, `Theta-svcomp-88`, benchcloud IDLE:
`pred_int`, `pred_bvms`, `kind_int`, `kind_bvms` (bitvector runs use **MathSAT**).

⚠️ **IDLE + four concurrent collections serialises them.** The vcloud scheduler fills machines in
submission order, so `pred_int` ran alone (3 h 07 m, done), `pred_bvms` is draining next
(14.5k/36.6k after 7.5 h → ~19 h), and both `kind` collections sat at **3 results each for 6+ hours**.
That is queue starvation, not a stall: all three clients are alive and healthy, and another user's
`cpachecker-por` job also outranks IDLE. Do not "fix" it by relaunching. Budget ~2 days wall-clock
for all four, or submit them one at a time.

### `pred_int` (PRED_CART / BW_BIN_ITP / `--arithmetic integer`) — COMPLETE

36,602 runs, score **8,856**: correct 6,122 (3,310 true / 2,812 false), wrong 32, error 30,132,
unknown 316.

**The integer encoding's real limit is the FRONTEND, not the solver.** Error profile vs run 87
(portfolio, `efficient`) on the identical task set:

| status | `pred_int` | run 87 |
|---|---|---|
| frontend failed, **before** parsing | **15,683** | 1,609 |
| server error | 4,449 | 0 |
| generic error | 1,996 | 5 |
| solver error | 1,773 | 199 |
| verification stuck | 448 | 0 |

**14,080 tasks parse under `efficient` but not under `integer`** — bitwise-heavy families:
`hardness` 6,343, `btor2c` 1,224, Juliet `CWE190`/`CWE191` 1,717, `linux` 655, `tdh` 492, `aws` 260.
Run 87 *solved* 3,427 of those 14,080 (2,478 true, 765 `false(no-overflow)`, 184 `false(unreach-call)`),
so this is lost coverage, not tasks that were hopeless anyway. Integer arithmetic is therefore not a
viable standalone config for the suite; its value is as a portfolio member on tasks it can express.

The 32 wrongs are all **known** families, no new class: `cstr*`/`openbsd*` alloca-string
`false(valid-deref)` 15 (the termination-15 bounds-across-call root cause above), `aws_linked_list_*` 3,
`2SB`/`4SB` wrong-`true`, `09-regions_*` wrong-`true` races 2, plus `scopes4-1`,
`ArraysOfVariableLength{,2}`, `memleaks_test11`, `test25-2`, `960521-1_1-2`, `test-0504{,_1}`,
`lockfree-3.0`, `rec_strcopy_malloc`.

Integer-encoding-specific error buckets worth a look **only if integer is kept in the portfolio**
(they do not affect the shipped `efficient` config): `server error` is 3,151/4,449 Juliet CWE190+191;
`generic error` is `minepump` 325, `email` 168, `pals` 131, `elevator` 90.

## ⚠️ RETRACTION: "termination-15 = a mid-object pointer loses its bounds across a call" is REFUTED

The root cause recorded earlier in this file (and its 9-line repro, `scratchpad/r4.c`) is **wrong**.
Instrumenting instead of extending the repro (`--output ALL`, reading the emitted `xcfa.c`) showed it
at once. Do not build on it.

**The repro was invalid.** It reads an *uninitialized* alloca cell:

```c
char *p = alloca(n); p[0] = '\0'; p += n - 1;   /* for n>1, p now points at an UNWRITTEN cell */
if (peek(p) == 'x') reach_error();              /* 'x' is a legitimate value -> Unsafe is CORRECT */
```

The bisect table claimed "read `*p` **in main** → Safe ✓, passed to a function → Unsafe ✗", and that
asymmetry was the whole basis of the conclusion. It does not exist: **both are Unsafe**, and the
in-main variant does not even use the pass that was blamed. Re-running a genuinely safe shape
(constant size, every cell written before the mid-object read) gives **Safe both in main and across a
call**, so a mid-object pointer survives a call fine. `seedSplitParams` is not implicated — its
premise ("passing a bare split variable is rejected outright") *holds*: multi refuses these programs.

**What actually happens on the real tasks.** `termination-15/cstrchr_reverse_alloca.i`
(valid-memsafety, expected `true`) reproduces as `false(valid-deref)` trace 7, and the log says:

```
note: frontend build failed due to a pointer-splitting limitation under --memory-model multi;
      retrying with --memory-model flat
```

So multi **refuses** (loudly, correctly), the CLI **silently falls back to flat**, and the wrong answer
is produced by *flat*. This is the same family as the run-62 "F1 flood" (81 valid-memsafety
false-derefs on the alloca/malloc string family under flat) — it is reaching us through the fallback
even though multi is the default.

**Leading hypothesis, NOT yet proven.** `FlatMemoryPass` documents its own soundness precondition:
each object owns `[id*STRIDE, id*STRIDE+STRIDE)` and addresses never collide *"as long as no object is
larger than FLAT_STRIDE cells"* (`FLAT_STRIDE = 1 shl 16 = 65536`). `alloca(length)` with symbolic
`length` up to `INT_MAX` violates it, and **nothing enforces or checks it**; `MemsafetyPass` then
recovers the base as `(addr / STRIDE) * STRIDE`, which for an in-object offset ≥ STRIDE truncates to a
*different* object's base, whose recorded size is 0 — making the `size <= offset` guard a tautology and
the bad-deref edge always enabled.

Evidence is suggestive but incomplete: a constant-size `alloca(100000)` (> stride) variant of the task
reproduces the false `Unsafe` (trace 5), but **both under-stride controls errored instead of proving
Safe** (`UnknownSolverStatusException` exit 221, and `alloca(100)+bound` hit the array-ext bug below),
so the stride link is not yet demonstrated by a clean A/B. Next step: get the actual counterexample
*values* out of the real task (higher log level / trace dump) and read the chosen `length` — do not
write more variants, that is what produced the retracted conclusion.

If the stride limit is confirmed, the honest fix is to **refuse** under flat when an object's size is
not provably < FLAT_STRIDE (error 0 beats wrong −16), and/or to stop the silent multi→flat fallback
from selecting a model that is unsound for the program in hand.

### NEW BUG: `array-ext` missing from the Z3 back-transformation

`Z3TermTransformer.toFuncLitExpr:373` — `NullPointerException: Unsupported function 'array-ext' in Z3
back-transformation`, exit **202 (server error)**. Same family as the `bit2bool` gap fixed in
`646ac3b51c`. Z3 introduces `array-ext` (the array extensionality witness) when reasoning about array
equality, so any model containing one is unrecoverable. Plausibly a real contributor to the
**4,449 server errors** in `pred_int`; worth checking against that bucket before fixing.

### MEASURED: the silent multi→flat fallback causes 18 of `pred_int`'s 32 wrong answers

Ran the frontend (`--backend NONE`, so it is fast and exact) over all 32 `pred_int` wrong runs and
counted which ones print `retrying with --memory-model flat`:

**fallback = 18, no fallback = 14, not found = 0.**

The 18 are the whole alloca-string family (`cstr{chr,cmp,cpy,cspn,len,ncpy,pbrk,spn}_{mixed,reverse}_alloca`,
`openbsd_cmemrchr-alloca-1` — 15 runs), the DLL pair `test-0504` / `test-0504_1`, `960521-1_1-2`, and
`aws_linked_list_init_harness`. **17 of the 18 are `valid-memsafety`**; only the aws one is unreach-call.

So: multi refuses these programs (a pointer-splitting limitation — loudly and correctly), the CLI
silently retries under flat, and flat is exactly the model with the known run-62 false-`valid-deref`
flood on this family. The fallback converts an honest refusal (score 0) into a confident wrong answer
(−16). That is the single largest wrong-answer source in this config, worth ~**+272** to remove.

**Do not "fix" this by chasing the flat bug first.** The specific flat mechanism is still unproven —
see the stride hypothesis above; every attempt to isolate it hit a *different* bug, which is itself
worth knowing about this family:

| config on `cstrchr_reverse_alloca` | outcome |
|---|---|
| efficient, unbounded (as shipped) | `false(valid-deref)` trace 7 — the wrong answer |
| efficient, `length` bounded ≤100 | `Unsupported function 'array-ext'` NPE, exit **202** |
| efficient, constant `alloca(100)` | `UnknownSolverStatusException`, exit **221** |
| efficient, `FLAT_STRIDE = 2^40` | no answer in 420 s |
| bitvector, unbounded | JVM **SIGSEGV** (exit 139, legacy Z3 native) |
| bitvector, bounded ≤100 | `Z3Exception: theory not supported`, exit **221** |

**Proposed fix (not yet implemented, needs the cost side measured first):** do not fall back to flat
for `valid-memsafety`/`valid-memcleanup`, where flat is known-unsound on this shape; let the multi
refusal stand instead. Before shipping, measure what the fallback currently *earns* on memsafety
properties — how many currently-**correct** memsafety runs also take it — because those would become
errors. Gate on that number, not on the +272.

### ATTEMPTED AND REVERTED: banning the multi→flat fallback under memory-safety properties

Implemented `mayFallBackToFlat && !checksMemorySafety` in `ExecuteConfig.frontend`
(`inputProperty == MEMSAFETY || MEMCLEANUP`), built, and verified it does exactly what was intended:

| task | property | before | after |
|---|---|---|---|
| `cstrchr_reverse_alloca` | valid-memsafety | fallback → `false(valid-deref)` (**wrong**, −16) | no fallback, **exit 210** frontend failed (0) |
| `test-0504` | valid-memsafety | fallback → wrong | no fallback, exit 210 |
| `aws_linked_list_init_harness` | unreach-call | fallback → builds | **unchanged**, still falls back, rc 0 |

**The canary gate went red: 260 PASS / 2 FAIL** (baseline for this build is 262/0):

- `c/libvsync/mcslock.yml` [valid-memsafety] → `Frontend failed!`
- `c/uthash-2.0.2/uthash_JEN_test5-1.yml` [valid-memcleanup] → `Frontend failed!`

Both are permanent zeros — `mcslock` TIMEOUTs on every property in *both* `pred_int` and run 87;
`uthash_JEN_test5-1` frontend-fails in `pred_int` and TIMEOUTs/OOMs in run 87 — so **no correct answer
is lost**, consistent with the 0/60 sample. But the change still removes frontend coverage: programs
that used to build no longer build, which is precisely what the canary suite exists to catch, and
there is no exclusion mechanism in the harness (the `recursified_geo1-u` precedent was a plain row
deletion). **Reverted rather than hand-edit the gate to suit the change** — a gate you edit to make
your own patch pass is not a gate.

**The measurement stands and the better design is now clear.** Do not re-attempt the ban. Instead
keep the fallback — so these programs still *build* — and make the unsound part of the answer honest:
under a flat-**fallback** run with a memory-safety property, a `false(valid-*)` verdict is exactly the
class flat is known to get wrong (run-62: incorrect-false 18→107), so downgrade it to
unknown/error rather than reporting it. That kills the 17 wrong answers, keeps every currently-correct
answer, and leaves both canaries green because the frontend still succeeds. A `true` verdict can stay:
the observed flat memsafety failure mode is false alarms, not missed bugs (the flat *unsoundness*
sightings in run 62 were `no-data-race`, a different property).

Where to implement: the verdict is produced downstream of `frontend()`, so the flag to thread is "this
XCFA came from the flat fallback" (set where `cConfig.memoryModel` is pinned to `flat` in the catch) —
consult it where the memsafety result is finalised. Needs the canary gate **and** a portfolio-config
check, since run 87 is the shipped configuration and these numbers are from `pred_int`.

⚠️ **Correction on that gate run — it was load-contaminated, my fault.** The same log also shows
`Fixtures: 43 PASS, 19 FAIL`, every failure `actual=OTHER` (no verdict produced at all) on fixtures
that have nothing to do with the change: `hex_float_constant`, `storage_class_register`,
`builtin_infinity`, `builtin_prefetch`, `undeclared_memory_functions`, … Cause: I ran
`buildArchiveTheta-svcomp`, `shadowJar` and `:theta-xcfa-cli:test` in the foreground **while the
sweep was running**, against the documented rule (8 GB cgroup — one theta at a time, never during a
canary sweep). The verdict fixtures simply ran out of time. The identical fixture set was
**62 PASS / 0 FAIL** on this very code earlier in the session.

The two *canary* FAILs above are still genuine: `Frontend failed!` is a deterministic outcome, not a
timeout, and both are memsafety/memcleanup — precisely the properties the change disabled the
fallback for. So the revert decision stands; only the fixture numbers in that run are noise.

Lesson for the next gate: do not start any gradle build while `run_canaries.sh` is live, and read
`Fixtures:`/`RESULT:` lines rather than the harness exit status (a trailing `echo` in the launching
command masked the nonzero exit here, exactly the failure mode already recorded for `grep -c`).

## Batch 89 RESULT — PRED_CART: integer vs bitvector(MathSAT), full suite

Both runs 36,602 tasks, 5 min / 7 GB, Skylake, `Theta-svcomp-88`, identical task set.

| | `--arithmetic integer` | `--arithmetic bitvector` (MathSAT) |
|---|---|---|
| score | 8,856 | **10,383** |
| correct | 6,122 | **7,270** |
| wrong | **32** | 76 |
| error | 30,132 | 28,820 |
| unknown | 316 | 436 |

**Bitvector wins overall (+1,527) but is not a strict improvement.** The transition matrix matters more
than the totals:

| transition | runs |
|---|---|
| error → correct | **2,724** (the win) |
| correct → error | **1,566** (the hidden cost) |
| error → wrong | 58 |
| wrong → error | 15 |

The 1,566 `correct → error` are not noise: 699 solver error, 562 TIMEOUT, 258 verification stuck,
28 OOM — and by property 905 valid-memsafety, 505 unreach-call. So bitvector buys ~2.7k answers the
integer encoding could not express and pays back ~1.6k that it could, mostly to solver cost.

### Where bitvector is newly WRONG — 60 runs, the thing to fix

By family: `chl-*.wvr` **14**, `uthash` 12, `aws` 6, `relu`/`count` 3 each, `float`/`inv`/`sqrt` 2 each.
By verdict: `false(valid-deref)` 21, `false(no-overflow)` 18, `false(unreach-call)` 14, `true` 5.

Two groups deserve attention:

1. **`chl-*.wvr` — 14 new `false(no-overflow)` false alarms** where integer merely TIMEOUTs. A single
   coherent family, so likely one bitvector-specific overflow-guard defect. **Highest-value bitvector
   follow-up.**
2. **9 wrong-`true` (−32 each), 4 of them `aws_*_negated` harnesses** — `aws_byte_buf_init_harness_negated`,
   `aws_byte_buf_init_copy_from_cursor_harness_negated`, `aws_linked_list_init_harness_negated`,
   `aws_string_new_from_array_harness_negated`. A `_negated` harness exists to *be* unsafe, so these are
   **missed bugs**, the worst failure mode. Also `2SB`/`4SB` and the two `09-regions` races (already known).

### Where integer is wrong and bitvector is not — 16 runs, and it is instructive

12 of the 16 are the `cstr*`/`openbsd*` alloca-string family: integer answers `false(valid-deref)`
(**wrong**, −16) while bitvector reports **`ERROR (solver error)`** (0). That is exactly the
wrong→error trade the reverted fallback ban tried to engineer, arriving here by accident — further
evidence that this family's wrong answers come from an unsound *model*, not from the property being
genuinely violated. `scopes4-1` (TIMEOUT) and `960521-1_1-2` (verification stuck) behave the same way.

### Reading

Neither encoding dominates. Integer's ceiling is the **frontend** (14,080 tasks it cannot parse at all,
see the `pred_int` entry above); bitvector's ceiling is the **solver** (699 solver errors + 562 timeouts
on tasks integer solved). They are complementary, which argues for keeping both in the portfolio rather
than picking one — but bitvector's 60 new wrongs, especially the 4 missed `aws_*_negated` bugs, must be
triaged before leaning on it further.

⚠️ Still pending: the KIND half. `kind_int` is running (22.5k/36.6k); `kind_bvms` still starved at 3.

### ROOT CAUSE (bitvector `chl-*.wvr`, 14 wrong): a mixed-width guard comparison is mis-encoded

The largest bitvector-only wrong family. **Not a regression from `c22f2d1988`** — run 87
(portfolio/`efficient`, which contains that fix) answers these **18 correct / 0 wrong**; only
`--arithmetic bitvector` gets them wrong. Encoding-specific.

Instrumented rather than guessed: the violation witness points at **`chl-collitem-subst.wvr.c:109`,
`return a - b;`** — the *guarded* subtraction inside `minus()`, not the guards themselves:

```c
int minus(int a, int b) {
  assume_abort_if_not(b <= 0 || a >= b - 2147483648);   /* RHS only when b > 0 */
  assume_abort_if_not(b >= 0 || a <= b + 2147483647);   /* RHS only when b < 0 */
  return a - b;                                          /* provably cannot overflow */
}
```

Those two guards are exactly sufficient (b>0 ⟹ a-b ≥ −2³¹; b<0 ⟹ a-b ≤ INT_MAX; b=0 trivial), so an
overflow report at line 109 means the guard constraints are not holding in the encoding.

**Minimal case — `scratchpad/guard_minus.c`, 10 lines, reproduces at trace 5:**

```c
int a = __VERIFIER_nondet_int(), b = __VERIFIER_nondet_int();
if (!(b <= 0 || a >= b - 2147483648)) return 0;
if (!(b >= 0 || a <= b + 2147483647)) return 0;
return a - b;                       /* bitvector: Unsafe(no-overflow) -- WRONG; efficient: Safe */
```

Trace **5** on a guarded subtraction ⇒ modelling bug, not imprecision.

**Mechanism:** under ILP32 the literal `2147483648` fits neither `int` nor `long`, so C types it
`long long`; `b - 2147483648` is 64-bit and the comparison `a >= (b - 2147483648)` must be evaluated
at 64-bit width after promoting `a`. Under bitvector it evidently is not — a 32-bit evaluation makes
the guard admit `a` values for which `a - b` really does overflow, and the subsequent overflow check
fires legitimately on a state the guard should have excluded.

**Two hypotheses were tested and REFUTED first** (do not retry them):
- literal typing alone — `long long g = b - 2147483648;` under `b > 0` is **Safe** in both encodings,
  so the literal is not being wrapped to `INT_MIN`;
- short-circuit handling — `(b >= 0) || (b + 2147483647 >= 0)` under `b > 0` is **Safe** in both, so
  the `||` short-circuit *is* honoured by the overflow instrumentation.

It is specifically the **mixed-width comparison** that breaks. Next step: dump the comparison's
encoded form under bitvector and check the promotion of the `int` operand against the 64-bit RHS —
suspect a `BvType` width unification that truncates to the narrower operand instead of promoting to
the wider. Fixing it should recover 14 wrong → correct in the bitvector configuration, and the same
guard idiom is used throughout `c/weaver/`, so the real reach is likely larger than 14.

#### ⚠️ CORRECTION to the entry above: the "mixed-width comparison" mechanism is DISPROVEN

Dumping the encoded form (`--output ALL`, `xcfa-main.smt2`) shows the 64-bit guard is encoded
**correctly**:

```smt
(bvsge ((_ sign_extend 32) |main::a|)
       (bvadd ((_ sign_extend 32) |main::b|) #xFFFFFFFF80000000))
```

`a` is promoted with a proper `sign_extend` and the literal is a 64-bit `-2^31`. The second guard is
32-bit `(bvsle a (bvadd b #x7FFFFFFF))`, which is also right — `b + 2147483647` genuinely *is* `int`
arithmetic in C. So the promotion is fine and my stated mechanism was wrong. The **observations**
in that entry still hold (bitvector wrong / `efficient` correct; witness at line 109 `return a - b`;
`guard_minus.c` reproduces at trace 5); only the explanation was premature. Do not build on it.

Also refuted, in addition to the two dead ends already listed: literal wrapping, `||` short-circuit
handling, and now operand promotion. Three mechanisms eliminated.

**Blocking obstacle for the next attempt:** narrowing to a single guard hits a **native crash**.
`g1.c` (guard 1 only, `b>0` forced — 8 lines) under `--arithmetic bitvector` with the default
**legacy Z3** dies with **SIGSEGV, exit 139**, "the monitored command dumped core", after the
frontend completes. Same crash seen earlier on `cstrchr_reverse_alloca` under bitvector. Both
single-guard reductions (`g1.c`, `g2.c`) are unusable for this reason, while `efficient` answers both
**Safe** in seconds. That native crash is a genuine bug in its own right and probably blocks other
bitvector triage.

⚠️ **Solver dimension not yet controlled.** The 14 benchmark wrongs came from `pred_bvms`, which uses
**MathSAT**; every local reproduction here used the **default legacy Z3**. Both produce a false
`Unsafe` on `chl-collitem-subst`, so the defect is unlikely to be solver-specific — but that has not
been verified, and the next attempt should pin the solver explicitly on both sides before drawing any
conclusion. Sequence for the next session: reproduce `guard_minus.c` under MathSAT, then diff the
encoded query against the `efficient` one, rather than reducing the program further (reduction is
what hit the segfault).

### Batch 89 — `kind_int` (KIND / `--arithmetic integer`) COMPLETE

36,602 runs, score **8,273**: correct 5,496, wrong 30, error 30,757, unknown 319.

Against `pred_int` (same encoding, same task set — so this isolates the **backend**):

| | PRED_CART | KIND |
|---|---|---|
| score | 8,856 | 8,273 |
| correct | 6,122 | 5,496 |
| wrong | 32 | 30 |

| transition | runs |
|---|---|
| correct → error | **2,213** |
| error → correct | **1,587** |

KIND scores lower overall but is strongly **complementary, not dominated**: it solves 1,587 tasks
PRED_CART cannot, while losing 2,213 it can. That is a real argument for keeping both in the
portfolio — the headline score difference (−583) badly understates KIND's contribution, because
~29% of what it answers correctly is outside PRED_CART's reach entirely.

Its wrong set is also the *smallest* of the three completed runs (30 vs 32 vs 76), so KIND is not a
soundness liability.

Remaining: `kind_bvms` (10.2k/36.6k, last one running) completes the 2×2 and gives the KIND half of
the integer-vs-bitvector question.

## ROOT CAUSE CONFIRMED (bitvector `chl-*.wvr`): `a - b` widens the negation AFTER it wraps

Supersedes the two earlier explanations in this file (both disproven — mixed-width comparison, and
before that literal wrapping / short-circuit). This one is confirmed by a concrete witness.

**Solver dimension controlled and eliminated** — same program, same solver, different encoding:

| encoding | solver | verdict |
|---|---|---|
| bitvector | Z3 (default) | `Unsafe` trace 5 — **wrong** |
| bitvector | **MathSAT 5.6.10** | `Unsafe` trace 5 — **wrong** |
| efficient | **MathSAT 5.6.10** | `Safe` — correct |

So it is the encoding, not the solver. (The 14 benchmark wrongs came from MathSAT; every local repro
had used Z3 — that gap is now closed.)

**Mechanism.** `BvOverflow.bvOverflowCondition` detects overflow by redoing the operation one bit
wider and checking the two agree. C spells `a - b` as an n-ary **`(+ a (- b))`**, so the subtrahend
arrives at `foldChecks` as a `NegExpr` and is widened with `widen(op, w)` = `SExt(bvneg b)` — the
negation is performed at the **narrow** width, where it wraps. `bvneg INT_MIN == INT_MIN`, so for
`b == INT_MIN` the "exact" reference value is `a - 2^31` instead of `a + 2^31`, the two sides differ,
and a spurious overflow fires. The emitted SMT shows it plainly:

```smt
(= ((_ sign_extend 1) (bvadd a (bvneg b)))
   (bvadd ((_ sign_extend 1) a) ((_ sign_extend 1) (bvneg b))))   ; <-- neg BEFORE widening
```

Note the real `SubExpr` branch (line ~102) is already correct — it widens both operands *then*
subtracts. Only the `Add`-of-`Neg` spelling, which is what C actually produces, is affected.

**Minimal witness — `scratchpad/negmin.c`, trace 5:** `a == -1`, `b == INT_MIN`;
`a - b == 2147483647` is in range, yet bitvector reports `Unsafe(no-overflow)` while `efficient`
reports `Safe`. `chl-*`'s `minus()` guards `a - b` and is called with unconstrained ints, so
`b == INT_MIN` is reachable — hence the whole family.

### ⚠️ First fix attempt FAILED — reverted, do not repeat it as-is

Added `widenOperand(e, to) = if (e is NegExpr) BvExprs.Neg(widenOperand(e.op, to)) else widen(e, to)`
and routed the reference side of `foldChecks`/`Sub`/`ShiftLeft` through it, deliberately leaving the
**narrow** side on `widen` (the wrapped value must keep wrapping). It compiles and is arguably the
right shape, but **`negmin.c` — three lines — then times out at 200 s** (rc 124) instead of answering,
and so do `guard_minus.c` and the real `chl` task. Trading a wrong answer for a non-terminating run is
not an improvement, so it was reverted; the tree is clean.

Why it hangs is the open question, and is the next thing to establish (do **not** just retry the
edit): the reference term becomes `bvadd (sext a) (bvneg (sext b))` where before it was
`bvadd (sext a) (sext (bvneg b))`. Suspect the predicate-abstraction refinement no longer finds an
interpolant it previously found. Worth checking first whether the *encoding* is now correct but the
*analysis* diverges — e.g. run the same query with `--backend BMC` or a bounded check, which does not
refine, to separate "formula wrong" from "CEGAR cannot refine it".

### RESOLVED: the fix is CORRECT — the hang is CEGAR refinement, not the formula

Supersedes "First fix attempt FAILED" above. Ran the fixed encoding under the **non-refining**
backends, exactly as that entry proposed, and the split is clean:

| `negmin.c`, bitvector | without fix | with fix |
|---|---|---|
| CEGAR / PRED_CART | `Unsafe` (**wrong**) | hangs (timeout) |
| **BMC** | — | **Safe** ✓ |
| **KIND** | `Unsafe` trace 4 (**wrong**) | **Safe** ✓ |

So `widenOperand` produces a *correct* formula; PRED_CART's predicate refinement simply fails to
converge on it. Clean A/B on the **same** backend (KIND, bitvector): without the fix `negmin.c` and
`guard_minus.c` both answer `Unsafe`; with it both answer `Safe`.

**Kept, per the standing rule** that a genuine fix stays even when it does not by itself produce an
answer — it converts a **wrong** answer (−16) into a timeout (0) under PRED_CART, and into a
**correct** answer under BMC/KIND, which are portfolio members. The remaining PRED_CART divergence is
a separate, now-isolated problem (interpolation over `bvneg` of a sign-extended operand), not a reason
to keep an unsound overflow check.

Guarded by fixture `bv_sub_intmin.c` (`SAFE:no-overflow`, `bitvector`, batch 89) — carries both the
minimal witness and the real `minus()` shape. The portfolio answers it `Safe` in well under the
fixture timeout, verified before the row was added.

Note the real `chl-collitem-subst` task still times out under KIND (3 threads); the fix removes the
*wrong answer*, and whether those 14 runs become correct in the portfolio is for the next benchmark
to say — do not assume +14.

## Batch 89 COMPLETE — the 2×2: {PRED_CART, KIND} × {integer, bitvector+MathSAT}

All four full-suite runs done, 36,602 tasks each, 5 min / 7 GB, Skylake, `Theta-svcomp-88`.

| config | score | correct | wrong | wrong-`true` (−32) |
|---|---|---|---|---|
| PRED_CART integer | 8,856 | 6,122 | 32 | 4 |
| PRED_CART bv+MathSAT | 10,383 | **7,270** | 76 | 9 |
| KIND integer | 8,273 | 5,496 | 30 | 4 |
| **KIND bv+MathSAT** | **10,629** | 6,876 | **29** | 12 |

**KIND+bitvector is the best configuration on both axes that matter** — highest score *and* the
fewest wrong answers (29 vs PRED+bitvector's 76), despite solving ~400 fewer tasks. That was not
visible from the partial data: on the integer side KIND looks strictly worse than PRED_CART
(8,273 vs 8,856), and the ordering reverses under bitvector.

Bitvector helps both backends, and helps KIND more cleanly:

| int → bv | error→correct | correct→error |
|---|---|---|
| PRED_CART | 2,724 | 1,566 |
| KIND | 2,500 | **1,119** |

### The wrong sets barely overlap — 22 of 83

`PRED-bv wrong = 76`, `KIND-bv wrong = 29`, **both = 22**, PRED-only = 54, KIND-only = 7. So most of
PRED+bitvector's extra wrongs are *backend*-specific, not encoding-specific, and KIND does not
inherit them. Combined with the near-identical wrong counts under integer (32 vs 30), the story is:
**bitvector is what unlocks tasks; PRED_CART is what turns some of them into wrong answers.**

### What the shipped `65e6119b87` should move

`chl-*` is **11 of KIND-bv's 29 wrongs** and 14 of PRED-bv's 76 — the largest single family in *both*
bitvector configurations, and the one the INT_MIN negation fix addresses. It is therefore the biggest
available win in the best-scoring config. (Still not to be assumed as +14/+11 — the fix removes the
wrong answer; whether each task then answers or times out is for the next benchmark.)

### Highest-severity remaining: 4 missed bugs, both bitvector configs

`aws_byte_buf_init_harness_negated`, `aws_byte_buf_init_copy_from_cursor_harness_negated`,
`aws_linked_list_init_harness_negated`, `aws_string_new_from_array_harness_negated` — all answered
`true` where the expected verdict is `false`. A `_negated` harness exists precisely to *be* unsafe, so
these are **missed bugs at −32 each**, the worst failure mode, and they are consistent across both
backends under bitvector (under integer these tasks fail at the frontend instead, which is why they
did not show up earlier). Next target.

Other KIND-bv wrong-`true`: `popl20-*` (3, weaver concurrency), `2SB`/`4SB` (known memory-model),
`09-regions_03-list2_rc` (known race), `cmp-freed-ptr`, `naturalNumbers1`.

### NEXT TARGET — 4 aws `*_negated` missed bugs (−32 each, both bitvector backends)

Reproduced locally on `aws_byte_buf_init_harness_negated.i` (LP64, bitvector, expected `false`):
**both** `CEGAR/PRED_CART` and `KIND` answer `Safe`. A missed bug, not a false alarm — the worst
failure mode, and consistent across backends, so it is a *modelling* problem rather than a search one.
(Under `--arithmetic integer` these tasks fail at the frontend instead, which is why they surfaced
only in the bitvector runs.)

**What must be reachable.** The harness body is:

```c
struct aws_byte_buf buf = {nondet_ulong(), 0, nondet_ulong(), 0};
struct aws_allocator *allocator = can_fail_allocator();   /* defined, returns &static */
size_t capacity = nondet_size_t();
if (aws_byte_buf_init(&buf, allocator, capacity) == 0) { ...negated asserts... }
```

and `aws_byte_buf_init` (defined at :7098, prototype at :4118 — normal order, so **not** the known
"prototype after definition wiped the body" bug) already contains a negated assertion of its own
before returning:

```c
buf->buffer = (capacity == 0) ? NULL : aws_mem_acquire(allocator, capacity);
if (capacity != 0 && buf->buffer == NULL) return -1;
buf->len = 0; buf->capacity = capacity; buf->allocator = allocator;
__VERIFIER_assert(!(aws_byte_buf_is_valid(buf)));      /* <-- must fire */
return 0;
```

So there is a **very short** unsafe path: `capacity == 0` ⇒ `buffer = NULL` ⇒ the `if` guard is false
(`capacity != 0` fails) ⇒ control falls straight into the inner assertion, with no allocation
involved at all. `__VERIFIER_assert` is defined here as `if(!cond){reach_error();abort();}`, so this
is plain reachability. Theta proving it `Safe` means it believes that path infeasible.

Given the path needs no allocator success and no heap reasoning, the suspects are, in order:
1. `aws_byte_buf_is_valid(buf)` evaluating to something that makes `!(valid)` true (check it directly
   — it is a small predicate over `len`/`capacity`/`buffer`);
2. the `assume_abort_if_not((buf))` / `assume_abort_if_not((allocator))` prologue killing the path;
3. the `?:` on `capacity == 0` being mis-folded (note `ca34ff467e` already fixed one ternary
   short-circuit defect — check whether this is a second shape rather than assuming it is not).

Start by dumping the XCFA for the harness and checking whether the `capacity == 0` branch and the
inner assert edge survive at all — do not write a hypothesis repro first.

## Debugging bitvector where integer is CORRECT (user request 2026-08-15)

The strict regression set — same task, `correct` under integer, `wrong` under bitvector — is **tiny**:

| task | property | integer | bitvector | backends |
|---|---|---|---|---|
| `aws_linked_list_init_harness_negated` | unreach-call | `false(unreach-call)` ✓ | **`true`** ✗ | **both** |
| `rule60_list2` | unreach-call | `true` ✓ | `false(unreach-call)` ✗ | PRED only |
| `linear_interpolation_2` | no-overflow | `true` ✓ | `false(no-overflow)` ✗ | KIND only |

Union of 3, one in both backends. So bitvector is **not** broadly less sound than integer — its extra
76/29 wrongs are overwhelmingly on tasks integer could not answer at all, not regressions.

### ✅ `linear_interpolation_2` is ALREADY FIXED by `65e6119b87`

Re-run locally after the INT_MIN negation fix: **both** encodings now answer `Safe` (it was
`false(no-overflow)` under bitvector in the batch-89 run). Independent confirmation that the fix
generalises beyond the `c/weaver/chl-*` family it was found on.

### `aws_linked_list_init_harness_negated` — reproduced, partially narrowed

Integer: `Unsafe` **trace 9** (correct). Bitvector: `Safe` (missed bug, −32). The harness is 3 lines:

```c
struct aws_linked_list list;
aws_linked_list_init(&list);                        /* head.next=&tail, head.prev=0,
                                                       tail.prev=&head, tail.next=0 */
__VERIFIER_assert(!(aws_linked_list_is_valid(&list)));
```

and `is_valid` returns `is_valid_deep(list)` only if
`list && head.next && head.prev==NULL && tail.prev && tail.next==NULL` — all of which hold after
`init`. Bitvector answering `Safe` means it evaluates that guard (or `is_valid_deep`) to false.

**Refuted:** that a pointer to **offset 0** (`tail.prev = &head`) tests as NULL under bitvector —
`scratchpad/ptr0.c` builds exactly that shape and is **Safe under both** encodings (KIND). So
offset-0 truthiness is fine; suspicion moves to `aws_linked_list_is_valid_deep` (a loop walking the
list) and to how the two encodings differ on the *empty-list* traversal.

⚠️ **New blocker for this family:** PRED_CART + bitvector on pointer/struct programs dies with
`Z3Exception: theory not supported by interpolation or bad proof`
(`Z3ItpSolver.getInterpolant:108`, exit **221**) — even on the 12-line `ptr0.c`. Use **KIND** for
bitvector pointer triage; PRED_CART cannot refine these at all. This is the third distinct
bitvector solver-infrastructure failure recorded (with the `array-ext` back-transformation NPE and
the native SIGSEGV) and is worth treating as its own work item — it likely accounts for a share of
`pred_bvms`'s 699 solver errors.

#### `aws_linked_list_init_harness_negated` — eliminations so far (NOT yet root-caused)

Confirmed reproduction: integer `Unsafe` **trace 9** (correct), bitvector `Safe` (**missed bug**,
−32), both backends, LP64, unreach-call.

The unsafe path requires `aws_linked_list_is_valid_deep` to set `head_reaches_tail`, which turns on
`temp == &list->tail` where `temp` was loaded back from `head.next`. If that comparison fails the
walk falls out with the flag clear, `is_valid` returns 0, `!(is_valid)` holds, and the negated
assertion passes — which is exactly the `Safe` bitvector reports. That is the shape to explain.

**Eliminated (do not retry):**

| hypothesis | test | result |
|---|---|---|
| offset-0 pointer tests as NULL under bv | `scratchpad/ptr0.c` | **Safe under both** — fine |
| mid-object pointer store + compare-back loses offset | `scratchpad/midcmp.c` (exact `head.next=&tail; temp==&tail` shape) | **Safe under both** — fine |
| the two encodings pick different memory models | both print `retrying with --memory-model flat` | **same model** — not it |
| structural difference in the built XCFA | `xcfa.dot` 50 lines for both | **identical size** — not it |

So the CFG and the memory model agree; the divergence is in *values*. From the emitted model
(`scratchpad/aws_integer/xcfa.c`) the relevant encoding is:

```
aws_linked_list_init_harness__list_ = 65536 * (__malloc + 1);   /* object base */
0[(+ list* 0)] = 65536 * (__malloc + 1);   /* head is its OWN sub-object, reached via a pointer cell */
0[(+ list* 1)] = 65536 * (__malloc + 1);   /* tail likewise */
0[(+ (deref 0 (+ init::list 0) Int) 0)] = init::list + 1;      /* head.next = &tail  ==  list + 1 */
```

i.e. `&list->tail` is `list + 1` (a *cell index*, not a byte offset), while `head`/`tail` themselves
are separate sub-objects behind pointer cells. The next step is to compare the **bitvector** model's
values for these same four assignments against the integer one — `xcfa.c` is not emitted under
bitvector, so read `xcfa.json`/`xcfa.dot` in `scratchpad/aws_bitvector/`. Suspect the interaction of
`65536 * (__malloc+1)` with the `+1` cell offsets once everything is Bv64 rather than unbounded Int.

⚠️ Use **KIND** for any bitvector experiment here: PRED_CART + bitvector on pointer/struct programs
cannot interpolate at all (`Z3Exception: theory not supported by interpolation`, exit 221) — it fails
even on the 12-line `ptr0.c`.

## ⚠️ CORRECTION (user, 2026-08-15): **bitvector + interpolation REQUIRES MathSAT**

Z3-legacy cannot interpolate bitvector theories. Every local CEGAR/bitvector experiment in the
sections above used the **default Z3** and is therefore invalid wherever interpolation was involved.
Always pass `--abstraction-solver mathsat:5.6.10 --refinement-solver mathsat:5.6.10` with
`--arithmetic bitvector` and a `*_ITP` refinement. (The batch-89 `pred_bvms`/`kind_bvms` runs already
did this — only the local reproductions were misconfigured.)

### What this changes

**1. `65e6119b87` is BETTER than its commit message says.** That message states CEGAR/PRED_CART "no
longer converges and times out" with the fix. **Wrong** — that was Z3 failing to interpolate, not
divergence. With MathSAT, PRED_CART answers **`Safe`** on both `negmin.c` and `guard_minus.c`. So the
fix is **wrong → correct** under the configuration the benchmark actually uses, not wrong → timeout.
The reasoning for keeping it stands; only the stated downside was imaginary.

The real `chl-collitem-subst` still **times out** at 280 s under PRED_CART+MathSAT with the fix
(it answered `Unsafe` — wrongly — before). So for that task the trade really is wrong → timeout; for
the minimal shapes it is wrong → correct. Whether the 14 benchmark runs land as correct or timeout at
300 s is still for the next benchmark to say.

**2. The "PRED_CART+bitvector cannot interpolate pointer programs" blocker was MY misconfiguration,
not a theta bug.** With MathSAT, `ptr0.c` returns a clean `NotSolvableException` ("Task is not
solvable with this configuration", exit **220**) instead of `Z3Exception: theory not supported by
interpolation`. Strike that item from the bitvector-infrastructure list.

**3. Re-check the other two "bitvector solver-infrastructure" findings before treating them as bugs** —
both were observed under Z3 with bitvector and may be the same misconfiguration:
- native **SIGSEGV** (exit 139) on `g1.c`/`cstrchr_reverse_alloca`;
- **`array-ext`** back-transformation NPE (exit 202) in `Z3TermTransformer`.
Neither has been retried with MathSAT. Do that before filing them as defects. (The `array-ext` NPE
may still be real for *non*-interpolating uses of Z3, and `pred_bvms`'s 699 solver errors came from
MathSAT runs, so that bucket needs its own look either way.)

**4. UNAFFECTED: the `aws_linked_list_init_harness_negated` missed bug is real.** Re-run under
PRED_CART + **MathSAT**: still `Safe` where integer says `Unsafe` (trace 9). The four eliminated
hypotheses recorded above stand.

### Retry of the two remaining "bitvector infrastructure" findings under MathSAT — verdicts

| finding | under Z3 (as first seen) | under MathSAT | verdict |
|---|---|---|---|
| native SIGSEGV, `g1.c` | exit 139, dumped core | **`Safe`** | **NOT a bug** — misconfiguration. Struck. |
| `array-ext` NPE, `bounded.c` | exit 202 | see below | **REAL** — see below |

**`array-ext` is a genuine defect and it is NOT bitvector-specific.** It reproduces under
`--arithmetic efficient` (which picks integer arithmetic here) with the **default Z3**, a
configuration where Z3 interpolation is fully supported — so the MathSAT correction does not excuse
it. That is also the configuration the shipped portfolio uses.

| config on `scratchpad/bounded.c` | outcome |
|---|---|
| efficient + default Z3 | `NullPointerException: Unsupported function 'array-ext'`, exit **202** |
| efficient + MathSAT | timeout (no error) |
| bitvector + MathSAT | `SmtLibSolverException`, exit 221 |

`array-ext` is Z3's array-extensionality skolem — the index witnessing that two arrays differ. It
appears in models whenever array equality/disequality is reasoned about, and
`Z3TermTransformer.toFuncLitExpr:373` has no handler, so it dies with a bare NPE. Exactly the same
shape as the `bit2bool` gap fixed in `646ac3b51c`.

Fixing it properly means back-transforming a skolem witness, which is not straightforward — a
reconstructed index must not silently claim a wrong value. The cheap, honest step is to replace the
bare NPE with a documented refusal naming the function (score is 0 either way, but the failure stops
looking like a crash). Sizing it first would be sensible: the `pred_int` server-error bucket is 4,449
runs and is dominated by Juliet CWE190/CWE191, so `array-ext`'s real share is unmeasured — the
per-run logs are zipped on benchcloud, so measuring it means pulling
`*.logfiles.zip` and grepping, not guessing.

**Also confirmed:** `cstrchr_reverse_alloca` is `Unsafe` trace 7 under **bitvector + MathSAT** too, so
that family's false `valid-deref` is encoding-independent — consistent with the multi→flat fallback
root cause recorded earlier, not with anything solver-specific.

## MEASURED: what the error buckets actually contain (from the zipped per-run logs)

Pulled by grepping `*.logfiles.zip` **remotely** on benchcloud (35 MB for `pred_int`, no transfer).

### `pred_int` (single config — counts ≈ runs)

| count | error |
|---|---|
| 8,117 | `UnsupportedFrontendElementException` |
| **4,752** | `IllegalStateException` **with no message at all** |
| 1,871 | `IllegalStateException: Non-bitvector type found!` |
| 1,589 | `UnknownSolverStatusException` |
| **3,788** | `No such method` — `memset` 1,373, `fscanf` 1,290, `fgets` 719, `calloc` 372, `_setjmp` 34 |
| **558** | **`array-ext`** back-transformation NPE |
| 624 | `No such variable or macro` (`SHAREX_*` 560, `malloc` 64) |
| 450 | `NotSolvableException` |

So **`array-ext` is sized: 558 runs** in this config — real and worth fixing, and it is the third
largest *fixable* single cause here.

Two larger items surface alongside it:
- **`No such method <libc>`, 3,788 runs.** `memset`/`calloc` are memory functions theta ought to
  model. Note the fixture `undeclared_memory_functions.c` already covers *undeclared*
  malloc/free/memcpy/memset being routed to the modelled ones — so this is a **different path**
  (declared-but-not-defined), not a gap in that feature. Worth checking why the routing does not
  apply.
- **4,752 bare `IllegalStateException` with an empty message** — the second largest bucket and
  completely undiagnosable as logged. Making these name their cause is cheap and would likely split
  this bucket into several actionable families.

### ⚠️ run 87 (shipped portfolio) — the same grep, but the counts mean something DIFFERENT

`fscanf` 109,445 · `calloc` 90,050 · `memset` 82,623 · `fgets` 62,660 · `_setjmp` 9,526 · `fopen`
7,239 · `tanhf` 3,479 · `memcpy` 3,326 · `expf` 2,484 · `sin` 2,344, plus 391,769
`ErrorCodeException` and 39,438 `UnsupportedOperationException`.

**Do not read these as run outcomes.** The portfolio tries config after config and each failing
sub-config logs its own error, so one task contributes many messages. The proof is in the XML:
run 87 has only ~**3,100** runs whose *final* status is an error (1,609 frontend-before, 1,322
frontend-after, 199 solver, 5 generic) out of 23,381 category=`error` — the rest are TIMEOUT/OOM.
So unmodelled libc functions mostly cost the portfolio **time** (each sub-config dies and the next is
tried) rather than directly costing score. That may still convert would-be answers into timeouts,
which is worth quantifying, but the headline counts must not be quoted as "82,623 tasks fail on
memset".

(`bit2bool` appears 3,182 times in run 87 and is already fixed in `646ac3b51c`, which post-dates that
run — a useful confirmation that this grep does surface real, fixable causes.)

## Batch 90 — diagnostics + libc audit (user request 2026-08-15)

### Q: what ARE the 8,117 `UnsupportedFrontendElementException`s?

**Essentially all of them are floating-point types under integer arithmetic** — not a defect:

| count | message |
|---|---|
| 4,198 | `Not (yet) implemented (CFloat …)` |
| 3,789 | `Not (yet) implemented (CDouble …)` |
| 130 | `Not (yet) implemented (CLongDouble …)` |

Everything else is in the tens: struct field not found 28, `typeof` over an undetermined type 25,
the inlining-arity refusal from `7976b40d75` (22 `printk`, 14 `dev_err`, …), byte-union float member
6, `fesetround` 3. So this bucket is the integer encoding declining floats, exactly as designed, and
is **not** an actionable error family.

### ✅ `array-ext`: clean refusal (both Z3 transformers)

The old `checkNotNull(model, "Unsupported function '…'")` reported a **NullPointerException** whose
message named the symbol — but the condition that actually failed was `model == null`, not the symbol
being unsupported, so the message was misleading as well as ugly. Replaced with an explicit
`UnsupportedOperationException` naming symbol **and arity** and saying why: no theta expression
corresponds to it and there is no model to interpret it against.

Deliberately **not** "fixed" by inventing an index: `array-ext(a,b)` is Z3's Skolem witness for array
extensionality (`a≠b → select(a,ext) ≠ select(b,ext)`), and substituting a fresh variable for a
Skolem changes what an interpolant means — trading a crash for a possible wrong answer.

### ✅ Bare `IllegalStateException`s now carry messages

Measured first: **4,728 of the 4,752** came from **one** site, `ExpressionVisitor#visitShiftExpression`,
and 24 from `CAssignment#getrExpression`. Both are `checkState(x instanceof BvType)` with no message,
and both fire for the same reason — **shifts and compound bitwise assignments are modelled only over
bitvectors**, so under `--arithmetic integer` the operands are unbounded `Int`s. All six call sites
now say that, and name the offending type and the flag to change.

### ❌ `calloc`: attempted, does NOT work, reverted

`calloc` is genuinely unmodelled (`malloc`/`realloc`/`memcpy`/`memset` all have passes; it does not).
Lowered it as `calloc(n,s)` → `malloc(n*s)` + `memset(p,0,n*s)` in a new `CallocFunctionPass` placed
before both — reusing tested machinery rather than open-coding, and inheriting `memset`'s
known-count restriction.

**It does not help.** `MemoryFunctionsPass.fill` needs the *pointee* type (`elementOf(dst)`), and
`calloc` returns `void*` — there is no element type at the call, so the fill gives up and the task
now fails with "No such method **memset**" instead of "No such method **calloc**". Verified on a
4-element `calloc` test: exit 202 either way. Reverted; the pass file is deleted and unwired.

**Why this is the byte-granular blocker again, not a missing pass:** memory is modelled as
`arrays[base][index]` over *typed* cells, so "zero N bytes" is only expressible once the element type
is known. `memcpy`/`memset` work because their destination is a typed pointer at the call site;
`calloc`'s is `void*` by its C signature. A correct `calloc` therefore needs either the byte-granular
model or the pointee type recovered from the *use* of the result — the same structural item already
recorded for intel-tdx and union punning. Do **not** re-attempt the malloc+memset lowering.

⚠️ Do not "fix" it by lowering `calloc` to plain `malloc`: freshly allocated cells are unconstrained,
so a program that relies on `calloc` zeroing would get a **wrong answer** instead of an error.

### The other unmodelled libc functions

`fscanf`, `fgets`, `fopen`, `_setjmp`, and the math family (`tanhf`, `expf`, `sin`) remain unmodelled.
These are **not** cheap to add soundly: `fgets`/`fscanf` write nondeterministic bytes *into a caller
buffer* (the same typed-cell problem as `calloc`), and `_setjmp` is non-local control flow. Modelling
any of them as a plain nondet return would be unsound — it would drop their memory side effects.
They are correctly failing loudly today; sizing before attempting is the right order.

### ✅ CORRECTION: `calloc` IS implementable — the earlier "reverted" entry above is superseded

I gave up on this too early. The types *are* available from metadata; the mistake was looking for them
in the wrong place, and then in the wrong scope.

**Two things had to be right:**

1. **Where the fill goes.** `calloc` returns `void *`, so at the call itself `pointeeOf` sees no
   element type and `MemoryFunctionsPass.fill` gives up. But the result is bound to a properly typed
   pointer (`int *p = (int *) calloc(...)`), and *that* expression carries the real `cType`. Emit the
   `memset` against the **binding**, not the call.
2. **Where to look for that binding.** It is on a **later edge**, not in the call's own label list —
   which is why the first two attempts still reported "No such method calloc". The pass now works in
   two phases over the whole procedure: replace each `calloc` with `malloc`, then scan for the
   assignment that references the result and insert the fill after it.

Also note the binding is `p = (T *) tmp`, a *cast*, not a bare `p = tmp`, so the match is on the
right-hand side **referencing** the result rather than being it.

**Verified in both directions** — this is the check that distinguishes a real fill from a vacuously
infeasible path:

| program | expected | got |
|---|---|---|
| `calloc(4,sizeof(int))`, assert `p[0]==0 && p[3]==0`, write/read `p[2]` | Safe | **Safe** ✓ |
| same, but `if (p[1] == 0) reach_error();` | Unsafe (calloc *does* zero) | **Unsafe** trace 6 ✓ |

Before the pass both were `exit 202, No such method calloc`.

Guarded by fixture `calloc_zeroes.c` (batch 90). Restriction retained deliberately: a statically
unknown count, or a result never bound to a typed pointer, is left alone and still fails loudly —
handing back a block that is silently not zeroed would be a wrong answer, not a missing feature.

`memset` itself was already implemented (`MemoryFunctionsPass`); what was missing was `calloc`
reaching it with a usable destination. The remaining unmodelled names (`fscanf`, `fgets`, `fopen`,
`_setjmp`, math) are still open and are a different problem — they write nondeterministic data into
caller buffers or move control non-locally.

## NEXT: `memset`/`memcpy` with a SYMBOLIC count — emit a loop instead of giving up

User direction (2026-08-15): stop `giveUp`ing on a symbolic byte count; emit a loop over the
elements of the pointee, sized by translating the byte count into an element count. Correct — and it
does **not** need the byte-granular model, which is what I wrongly implied when I called this
blocked.

**Why it currently fails.** `MemoryFunctionsPass` has implemented `memset` since batch ~60, but
`elementCount` (line ~346) requires `literalValue(bytes)`, so a symbolic `n` returns null and
`giveUp` leaves the `InvokeLabel` in place. The analysis then reports **"No such method memset"** —
a misleading message, since the pass *saw* the call and declined it. 1,373 runs in `pred_int`;
82,623 message occurrences in run 87 (that second figure is sub-config noise, not runs — see the
caveat above).

**Design.**

```
i = 0
while (i < n / w) { dst[i] = filler; i = i + 1 }     // w = sizeof(element), integer division
```

- `n / w` is computable symbolically — `Div` on the count expression — so nothing needs to be known
  at build time. Partial fills of an array (`memset(arr, 0, k)` with `k < sizeof arr`) fall out
  naturally: the bound is just smaller.
- Needs new locations + edges inside the pass. Precedent: `MemsafetyPass` (`XcfaLocation(...)` at
  :108/:192/:294/:334) already builds branch structure this way.
- Keep the existing constant-count path: it emits straight-line assignments, which the analyses
  handle far better than a loop. The loop is the fallback, not the replacement.

**⚠️ Soundness subtlety not to skip — the partial tail.** When `n % w != 0` the last element is only
*partly* covered. Filling `floor(n/w)` elements leaves that element holding its **old** value, but a
real `memset` overwrote some of its bytes — so the model would carry a specific *wrong* value, which
can both miss a bug and invent one. The tail element must therefore be **havoc'd**, not left alone:
unconstrained is an over-approximation and safe, the stale value is not. (This is the one place the
byte model would do better — it would fill exactly.)

**⚠️ Pass-order consequence.** `MemoryFunctionsPass` runs at position 133, *after* `LoopUnrollPass`
(69), so a loop introduced here is **never unrolled** — it reaches the analyses as a real loop. Fine
for KIND/BMC/IMC; CEGAR must then find an invariant for a fill loop it previously never saw. Measure
that rather than assume it: the honest comparison is against today's baseline of an outright error
(score 0), so even a timeout is not a regression, but a *new* class of CEGAR divergence would be.

Also worth doing at the same time and cheap: make the remaining `giveUp` cases say so. Reporting
"No such method memset" for a call the pass deliberately declined is the same diagnosability defect
just fixed for the bare `IllegalStateException`s.

### ✅ IMPLEMENTED: symbolic-count `memset` emits a loop

Supersedes the "NEXT" design entry above. `MemoryFunctionsPass` now lowers a `memset` whose byte
count is not known at build time into a real loop over the elements it covers:

```
i = 0;  while (i < n / sizeof *dst) { dst[i] = c; i = i + 1; }
```

The byte count needs only to be *translated* into an element count — an ordinary division — so
nothing has to be known statically and the byte-granular memory model is **not** required (my earlier
claim that it was is withdrawn). A partial fill of an array falls out of the same bound.

Verified both directions (the check that separates a real fill from an unreachable path):

| program, symbolic `n`, count `n * sizeof(int)` | expected | got |
|---|---|---|
| `memset(p,0,n*4)` then assert `p[0]==0` | Safe | **Safe** ✓ |
| same, but `if (p[0]==0) reach_error()` | Unsafe | **Unsafe** trace 10 ✓ |

Both were `exit 202, No such method memset` before. Gate: 262 canaries / 65 fixtures / 0 FAIL,
fixture `memset_symbolic.c`.

**The straddled tail is havoc'd**, guarded on `count * w == n` so the exact case keeps its precision —
leaving it with its stale value would be a specific wrong value, not a safe over-approximation.

**Two things learned building it:**
- Every edge label must be a `SequenceLabel`. Bare `StmtLabel`s on the assume edges made
  `UnresolvedInvokeToHavocPass` → `splitIf` fail its `check(label is SequenceLabel)` — surfacing as
  `IllegalStateException: Check failed`, exit 210.
- **CEGAR/PRED_CART times out** on the symbolic case: the pass sits at position 133, after
  `LoopUnrollPass` (69), so this loop is never unrolled and CEGAR must invent an invariant for it.
  KIND/BMC/IMC answer it. Against a baseline of an outright error (0) that is not a regression, but
  the win is backend-dependent and the portfolio must reach a loop-capable config.

⚠️ **`--backend NONE` runs the full pass pipeline**, so parse-only runs *do* exercise all of this —
they are not "frontend only" in the sense of skipping passes. Run 91 was launched before this landed
and was therefore stopped and relaunched rather than kept.

## Batch 91 — the run-91 parse regression, and three of the four error families

### ⚠️ Run 85 was DOUBLE-COUNTED in my first comparison (user caught it)

My run-85 figures came from an inline script that globbed **all 55** `*.xml.bz2`, with none of the
runset/block-level dedup `psum.py` does — counting most runs twice (72,103). Deduped it is **36,602**,
the *same task set* as run 91, so the two are directly comparable after all and my "different task
sets, not comparable" was wrong.

| status | run 85 | run 91 | Δ |
|---|---|---|---|
| built OK | 31,472 | 30,744 | **−728** |
| frontend failed, before parsing | 1,878 | 1,565 | −313 ✓ |
| frontend failed, **after** parsing | 1,352 | 2,260 | **+908** ✗ |

Per-task diff: **920 regressed** (built → failed), 193 improved.

### ROOT CAUSE of the regression: my own arity guard was too broad

`7976b40d75` refused **any** arity difference. But the loop walks `calleeParams` and indexes
`invokeLabel.params[i]`, so only a callee with **more** parameters than the call site supplies can run
off the end. A call site supplying *extra* arguments is every variadic call — `printk(fmt, ...)`,
`dev_err`, `__dynamic_dev_dbg` — which indexes safely and ignores the surplus, exactly as it did
before the guard existed. Refusing those cost **713 runs** (printk 476, dev_err 158,
__dynamic_dev_dbg 79), the bulk of the 839 after-parsing regressions, concentrated in LDV drivers.

Narrowed to `calleeParams.size > invokeLabel.params.size`. Verified: a regressed
`205_9a…cdc_eem.ko` task returns `ParsingResult Success`. **Same mistake as the reverted flat-fallback
ban** — a guard written for one observed shape and applied wider than the evidence supported. No
canary covers a variadic call into an undefined callee, which is why the gate stayed green.

### The other families

| family | count | status |
|---|---|---|
| inlining arity | 713 | **FIXED** (above) |
| `lhs is a BvPosExpr / BvSignChangeExpr` | 325 | **FIXED** — a promotion/signedness wrapper on the *lvalue* names the same storage as the variable underneath, so the assignment is built against the peeled variable with the value converted to *its* type. Verified: the probe task moves past it to an unrelated `typeof` limitation. |
| `__VERIFIER_nondet_memory with arguments` | 167 | **FIXED** — a pass-ordering bug. `NondetFunctionPass` (80) demands exactly one parameter and rejected it before `MemoryFunctionsPass` (133) could act; and `nondetFill` bailed out unless the *bytes* model was on. It now fills element cells under the typed-cell models too (byte count ÷ element width, the same translation `fill` does), and `NondetFunctionPass` defers in every memory model. |
| `non-constant dereference offset` | 213 | **NOT fixed, deliberately** — see below |

**Why the non-constant offset is left alone.** It is already a *documented refusal*, not a crash. The
offsets are pthread array handles indexed by a loop variable that `PthreadArrayHandleUnrollPass` did
not unroll: `(mod main::forN::i N)` 306, `(mod main::i N)` 28, `(mod t_fun::i N)` 22. Resolving them
would mean giving `&t[i]` a thread identity for symbolic `i`; mapping them all to the base variable
would **merge distinct threads**, which is exactly what makes racing tasks answer wrongly (the
`mutex1`/`mutex2` constraint). That is a real analysis feature, not a pass tweak, and a wrong answer
is worse than the honest refusal already in place.

### Host note
The machine was wiped mid-session again: **no JDK, gcc, python3, unzip, bzip2 or jq**, and `/tmp`
(scratchpad, generated TSVs) gone. `./gradlew` fails with "JAVA_HOME is not set" — and a build whose
output is grepped only for `^e:` will look like it *succeeded*. Reinstall with
`sudo apt-get install -y openjdk-21-jdk-headless gcc python3 unzip bzip2 jq`. The repo,
`benchmark-results/` and `sv-benchmarks` survive.

## Batch 92 — the 10-item frontend plan (user-sequenced 2026-08-19)

Worked ONE AT A TIME, each gated on `run_canaries.sh "" parse` (262 canaries + 65 fixtures) AND the
per-module unit tests, then committed before the next is started. Cron `288bf05b` re-enters this every
5 h so an interrupted session resumes here. Items marked **[subagent]** are to be delegated with fresh
context, per the user; gate and commit their work in the main session.

Baselines to beat: run 94 parse-only = **31,984 built OK**, 1,492 frontend-before, 850 frontend-after.
Run 93 full portfolio = score 19,804, 57 wrong, 18 missed bugs.

| # | item | why it is here | status |
|---|---|---|---|
| 1 | **[DONE]** print the offending TYPE in `Non-array expression used as array!` (was Q2) | the message names nothing, so the family cannot be triaged at all | |
| 2 | **[DONE]** struct expanded mid-definition was cached stale (was Q3; NOT 'collection stops' -- re-entrant expansion via a fn-pointer member's typedef) | `cert_st` defines `key, valid, mask, export_mask, rsa_tmp, rsa_tmp_cb, dh_tmp, dh_tmp_cb, pkeys[5], references`; theta collected exactly `[valid, export_mask, key, mask, rsa_tmp]` and dropped everything from `rsa_tmp_cb` on. 28 runs directly, and very likely the SAME root cause as item 3 below | |
| 3 | **[DONE -- no code needed]** fn-pointer through a `Dereference` (was Q8): measured against the pre-fix jar, already fixed by the earlier declarator fix; all 34 distinct families re-run, zero remain | `isCallableFunctionPointer` gates on the TYPE, not the shape -- candidate sets could dispatch any expression. These 79 are a `Dereference` whose cType lost its function-pointer-ness, i.e. probably item 2's bug. **Re-measure after item 2 before doing any work** | |
| 4 | **[DONE]** peel `BvPosExpr`/`BvSignChangeExpr` in the remaining lvalue shapes (was Q7). Residue is a DIFFERENT bug: they peel to `BvExtractExpr (Bv 1)` = single-bit bitfield writes, all intel-tdx -- likely dissolves under item 10 | the branch peels to `RefExpr`/`Dereference`; 94 runs peel to something else. Item 1's type printing should reveal what | |
| 5 | **[DONE]** give every DECLARED-but-not-defined function a referencable id (was Q6). Cause was the name PRE-PASS only walking definitions + reordered global decls; also closed a soundness hole where the id var was left unconstrained | only *defined* functions get an id, so `= malloc` / `= __VERIFIER_nondet_int` resolve to nothing (96 runs). Must work when a function is declared MORE THAN ONCE | |
| 6 | **[DONE]** inline a void call that does not pass the synthetic return slot (was Q4). Fixed in the INLINER, not by removing the slot -- the pipeline assumes a ret var exists | `void outb(unsigned char, unsigned int);` is declared with 2 params and every call passes 2, yet the callee arrives with 3 -- the arity guard then refuses (30 runs). The C is consistent; the mismatch is ours | |
| 7 | **[DONE]** switch to the bitvector encoding when a bitwise op needs it (was Q1). The fallback already existed at `XcfaParser.kt:267` and was DEAD: `FunctionVisitor` resolves `efficient` into integer/bitvector *before* the parse can fail, so the retry's `== efficient` guard was never true. Root cause underneath it: `BitwiseChecker` had no `visitAssignmentExpression` at all -- the grammar routes `x |= y` through `assignmentOperator`, not `inclusiveOrExpression` -- so a program whose only bit manipulation is compound looked purely arithmetic, integer was chosen, and `CAssignment` then refused the first `|=` under an encoding the frontend itself had picked. Also fixed: the four bitwise visitors descended into operand 0 only, leaving later operands unanalysed | `|=`, `>>=`, `<<=` and friends are only modelled over bitvectors; under `--arithmetic integer` there is no bit representation. Rather than refuse, fall back to bitvector for that task | |
| 8 | **[DONE]** `Array with unspecified size must have initializer list` (was Q5). All 112 runs are `extern T a[];` -- a DECLARATION, not a definition (C17 6.9.2p2), whose extent lives in another TU and is unknowable here; 73 such declarations over 11 names across the 56 tasks, 100% extern, none defined in-file. Fix: give the object its base, invent no extent, skip the initializer sweep, and register a FLAT_STRIDE memsafety bound (an unregistered base reads back as size 0, which makes every access an invalid deref). ⚠️ The bound is deliberately the PERMISSIVE direction -- it can miss a real OOB on such an array, but the alternative invents an extent and produces wrong `false(valid-deref)`. Tentative definitions and flexible array members still refused, now by name | could not reproduce from logs -- the message truncates on `CArray.toString()`. Reproduce locally first, then decide the correct behaviour | |
| 9 | **[DONE]** intel-tdx `ClassCastException: Expected (Bv 32), got (Bv 64)` (was Q9). TWO width bugs, one per data model. (a) `unsigned long` is 64-bit only under LP64, so "the unsigned type of width n" returned a type HALF the requested width under ILP32 and the union layout addressed past the cell (`_LARGE_INTEGER`, ldv drivers); now falls through to `unsigned long long` only where `unsigned long` is too narrow. (b) A union member that is a packed word of bitfields is stamped with the STRUCT's C type (so `.f` resolves as a field) and every aggregate reports a pointer-width placeholder as its SMT sort -> 64-bit value into a 32-bit cell (intel-tdx `keyid_ctrl.command = 1`); the splice now uses the unsigned type of the CELL's width, keeping the recorded type and still reporting when no C type matches. intel-tdx 210->0; ntdrivers advances to the separate `Could not handle left-hand side` family, so <298 runs are converted | 149 tasks x 2 configs, 62% intel-tdx. The archived XML truncates the message and no logfiles were kept, so it had to be reproduced locally | |
| 10 | **[DONE -- implemented, measured, and DELIBERATELY NOT SHIPPED]** fall back to `--memory-model bytes` when a failure says the bytes model would fix it (was Q10). The fallback works (guards correct, 3 float-newlib tasks 210->0), but the model it falls back INTO is unsound for the very pattern that triggers it, so shipping it would convert ~554 score-0 ERRORs into wrong `false` verdicts at -16 each. Reverted; repro kept at `canaries/fixtures/union_double_punning_bytes_UNSOUND.c` | ⚠️ the bytes model IS implemented on this branch; the fallback is a ~40-line mirror of multi->flat. The blocker is soundness, not wiring | |

### The fp round-trip's cost: NaN payloads (measured 2026-08-20, AFTER f470a74ddf)

Asked whether the unshipped bytes fallback would only ever produce ERRORs after the round-trip fix,
or could produce wrong verdicts. **It can produce wrong verdicts.** Measured, not reasoned:

    u.words[1] = 0x7FF80000u; u.words[0] = 0x2Au;  /* a NaN with payload 42 */
    double d = u.value;  u.value = d;              /* out through the float view and back */
    if (u.words[0] != 0x2Au) reach_error();

gcc: SAFE. theta under `--memory-model bytes`: **`SafetyResult Unsafe`** -- a spurious
counterexample, i.e. a wrong `false` (-16), not an ERROR (0).

Cause -- **corrected 2026-08-20 after checking the primary sources**, an earlier note here blamed
the canonicalization and that was wrong. The payload cannot survive a float round trip at all,
canonicalization or not, because SMT-LIB's FloatingPoint sort has **one** NaN element. Measured
against z3 4.12.6:

| query | result | meaning |
|---|---|---|
| `fp.isNaN x` and `fp.to_ieee_bv x != #x7FF8...0` | **sat** | the bits of a NaN are NOT pinned to the canonical pattern; the solver may choose |
| two distinct NaNs whose `fp.to_ieee_bv` differ | **unsat** | it IS a function -- every NaN maps to the same bits, so payloads collapse |
| `fp.to_ieee_bv((_ to_fp 11 53) #x7FF8...2A) != #x7FF8...2A` | **sat** | a payload round trip MAY lose the payload ... |
| the same, asserted equal | **sat** | ... and may keep it. Purely the solver's choice |

So in a verification query the solver is free to pick the representative that falsifies the property,
and it will. Our `Ite(IsNan, canonicalNaNBits, ToIeeeBv)` only makes that choice *deterministic*
(and consistent across solvers); the verdict on the repro is Unsafe with or without it. The
regression is caused by floats now travelling through IEEE bits at all, not by the guard.

Z3's own header (`z3_fpa.h`, `Z3_mk_fpa_to_ieee_bv`) reads: "IEEE 754-2008 allows multiple different
representations of NaN. This conversion knows only one NaN and it will always produce the same
bit-vector representation of that NaN." That is consistent with the table -- "one NaN" is the single
NaN *element of the sort* (row 2), not a bit pattern fixed by the theory (row 1).

⚠️ **This is a REGRESSION from f470a74ddf, and was verified as one** by rebuilding the parent commit:
before the fix this program verified **Safe**, because a float write did not touch the byte cells at
all, so the payload written through the integer view survived. That was luck, not soundness -- the
same non-aliasing is what made `u.value = 1.0; u.parts.msw` unconstrained and Unsafe. So the fix
trades a broad wrong-answer class (all punning of ordinary values, the newlib idiom) for a narrow one
(NaN payload preservation). Net positive, NOT strictly better, and worth saying out loud.

No cheap repair: an exact to-bits direction is what is needed and SMT-LIB does not specify one.
Peeling `ToIeeeBv(FromIeeeBv(b))` only catches a write whose right-hand side is syntactically the
read; here the value passes through a local first.

Repro: `canaries/fixtures/union_nan_payload_bytes_KNOWN_WRONG.c`, unregistered on purpose.

**Not reachable in anything shipped**, including runs 96/97: `bytes` needs an explicit
`--memory-model`, and the automatic fallback to it stays unshipped. So the answer to "errors only?"
is: on MathSAT yes, loudly (both conversion directions throw at encoding time); on a Z3 config the
round trip works and is correct for ordinary values, but NaN payloads are silently wrong.

## Run 100 (TARGETED Juliet, LOW) RESULT -- 2026-08-21, build 4f41483289

912 tasks instead of 36,602, at the user's suggestion: re-run exactly the family that turned wrong
rather than waiting on a full portfolio run to test a hypothesis about 456 tasks. Same options,
limits and portfolio as `theta27-long900.xml`, so the verdicts compare directly to run 98.
XML: `xmls/theta27-juliet.xml`; sets: `sv-benchmarks/c/juliet_offenders.set`, `juliet_controls.set`.

| group | n | run 98 | run 100 |
|---|---|---|---|
| offenders (Juliet CWE190 `_good`, expected **true**) | 456 | **456 wrong** | **456 correct** |
| controls (matching `_bad`, expected **false**) | 456 | 456 correct | **456 correct** |

Every single offender flipped `wrong -> correct`, and **not one control regressed** -- the range
bound removes the false alarms without suppressing the real overflows. That control group is the
point of the run: the offenders alone could not distinguish "fixed" from "stopped detecting
overflows", and a missed bug costs -32 where a false alarm costs -16.

Family score: **-7,296 -> +912, a swing of +8,208.** That number is now MEASURED for this family
rather than extrapolated from the 25-task sample. Run 99 (full portfolio, IDLE, same build) is still
queued and will say whether the rest of the benchmark moves with it; run 98's 13,407 plus this
family's swing would be ~21,615 against run 93's 19,835, but the rest of the run is not measured yet
and that figure stays a projection until run 99 lands.

⚠️ Still unexplained: WHY the bound changes these verdicts. Five minimal programs of the obvious
shape verify Safe with and without it. The fix is protected only by this real-task evidence -- there
is no fixture -- so a refactor could silently undo it.

## Run 99 (full portfolio, COMPLEX27) -- launched 2026-08-21 17:56, benchcloud

Tool dir `Theta-svcomp-99` = HEAD `4f41483289`. Same XML, priority (IDLE), CPU model (Skylake) and
client heap as run 98, so the two are directly comparable. Screen `theta-portfolio99`, outdir
`results/Theta-svcomp-99/theta27-long900.xml/2026-08-21_17:56:56/`. Launch checks: 0
`Cannot start process`, 0 `OutOfMemoryError`.

On top of run 98's build:
- the two `Could not handle left-hand side` fixes (`1b22c445da`) -- bitfield through a narrowing,
  struct copied through a pointer (~216 of the 224 runs in that family)
- the library-stub havoc bounded to the C type it writes (`4f41483289`)

**What this run is measuring.** Run 98 scored 13,407 against run 93's 19,835, and 456 of its 476 new
wrong verdicts were the Juliet CWE190 `_good` family answering `false(no-overflow)`. The stub fix
turned 25 of 25 sampled tasks from that family correct, with all 8 sampled `_bad` counterparts still
caught. **Do not quote a projected score from that sample** -- this run exists to replace the
projection with a measurement. The arithmetic that the sample suggests (~+8,200 over run 98, i.e.
comfortably past run 93) is a hypothesis for run 99 to confirm or refute, nothing more.

Baselines: run 93 = 19,835 / 55 wrong (complex26); run 98 = 13,407 / 528 wrong (COMPLEX27).
Note run 93 is still a complex26 baseline, so any difference against it other than the families
named above confounds portfolio with fixes; run 98 is the clean like-for-like comparison.

## Run 98 (full portfolio, COMPLEX27) RESULT -- finished 2026-08-21

| | run 93 (complex26) | run 98 (COMPLEX27) | delta |
|---|---|---|---|
| **score** | 19,835 | **13,407** | **-6,428** |
| correct | 12,890 | **13,905** | +1,015 |
| error | 23,173 | 21,684 | -1,489 |
| **wrong** | 55 | **528** | **+473** |

**The headline is misleading and the classification matters.** Of the 476 NEW wrong results, **475
were ERRORs in run 93** (score 0) and exactly **one** was previously correct. This is latent
unsoundness EXPOSED, not caused: tasks that used to fail now produce a verdict, and it is wrong.
Direction: 467 wrong-`false` (-16), 9 wrong-`true` (-32).

**It is not the portfolio.** Same build under `--portfolio STABLE` and `--portfolio COMPLEX27` gives
the identical wrong verdict on these tasks, so the complex26 -> complex27 switch is exonerated; the
cause is this batch's frontend work.

**It is one family: `Juliet_Test` + `no-overflow`, 456 of the 476, costing -7,296.** All are
`CWE190_Integer_Overflow__*_good` variants of the shape

    data = 0; fscanf(stdin, "%ld", &data);
    if (data < 0x7fffffffffffffffLL) { result = data + 1; }   /* provably safe */

theta answers `false(no-overflow)`. Bisecting the REAL file: emptying `goodB2G` -> Safe; removing
only the `fscanf` call -> Safe; removing only the `printLongLongLine` call -> still Unsafe. So the
trigger is the `fscanf` stub introducing an unconstrained value, after which the guard fails to keep
the addition safe. **The precise trigger is NOT yet isolated** -- minimal reproductions of that exact
shape (both `long` and `long long`, both data models) all verify Safe, so something else in the real
file participates. Three hypothesis repros failed; the next step is instrumenting the real input, not
a fourth.

**Mitigation, measured:** commenting the four `scanf`-family entries out of `LibraryStubsPass.STUBS`
returns these tasks to `No such method fscanf`, i.e. ERROR / score 0 rather than -16.

    run 98 as measured                                  13,407
    run 98 with the Juliet/no-overflow wrongs as ERROR   20,703   (+868 vs run 93)

So **the batch is net positive (+868) once this one family stops answering wrongly** -- the +1,015
extra correct results are real. Two ways forward: fix the false alarm (better), or gate the
scanf-family stubs off until it is fixed (cheap, recovers ~7,300 immediately). Not decided here.

⚠️ Also note run 93 is a complex26 baseline; the portfolio differs. The A/B above shows the portfolio
is not responsible for THIS family, but any other comparison against run 93 still confounds the two.

## `Could not handle left-hand side of assignment` -- debugged 2026-08-20 (commit 1b22c445da)

One message, **two unrelated bugs**, 224 runs in run 96. The type printing added by item 1 is what
separated them; the message now also names the C types of both sides, and names a struct by its
FIELDS (two different structs otherwise both print as `CStruct`, which was itself misleading).

| shape | runs | cause | status |
|---|---|---|---|
| `ctls.some_bit = ...` (intel-tdx) | ~144 | `structuralBitfieldWrites` looked ONE level down, expecting the 1-bit extract to sit on a dereference/concat. Reading a bitfield out of a 64-bit cell narrows to 32 bits first, so the operand is another extract | **FIXED** -- fold the narrowing chain, `extract(extract(X,a,b),c,d)` = bits [a+c, a+d) of X, guarded against reaching past the inner extract or past the cell |
| `*(list+i) = *(list+j)` (ldv-linux-*) | ~72 | the struct-copy guard demanded the lvalue's cType BE a struct; dereferencing a struct pointer yields the element's address, whose cType is the POINTER's | **FIXED** -- accept the pointee, only when the rhs is that same struct |
| `Toc->TrackData[0] = Toc->TrackData[i]` (ntdrivers) | 8 | the RIGHT-hand element address loses its struct cType (identity-keyed metadata); `getType` then derives `CUnsignedInt` from the (Bv 32) sort, so the sides disagree | **NOT FIXED** |

A/B, rebuilt each way: `tdh_mng_key_config__invalid_input_tdr_hkid` and `module_get_put-drivers-atm-eni`
both 210 -> 0.

⚠️ **The attempted fix for the last 8 was reverted, and the reason is worth keeping.** C requires a
struct lvalue's rhs to be that same struct (6.5.16.1), so "accept an address-shaped rhs whose type did
not survive" looked safe. It is not: a *derived* type cannot be told apart from a real one, so the
rule also swallowed `CPointer` right-hand sides into `structCopy` (ClassCastException) and regressed
tasks that had begun building. The fix belongs where that element address is built, by keeping the
struct type on it.

⚠️ **Latent, found on the way and NOT chased:** `CComplexType.getType` returned different answers for
the same expression on successive calls (`CUnsignedInt` then `CStruct`). That instability is why an
earlier guard appeared to contradict itself, and it likely explains other identity-keyed metadata
surprises. Worth its own investigation.

⚠️ **Yield could not be measured locally.** This host had ~9 GB of 62 free; 18 of the 24 *smallest*
files in the family were SIGKILLed and 21 of 30 in the first sample. Of the 6 that did complete, none
still failed on this message. The real number needs a benchmark run.

## Local parse-only check of the byte-addressed union family (2026-08-20, build e07b3354df)

User asked whether that family is "mostly handled" now that the fallback ships. **It is not.**
Measured, stratified sample of **105** of the 724 distinct (file, property) pairs, run locally with
`--backend NONE` on the build that has the fallback:

| half of the family | n | built OK (exit 0) | fell back | outcome |
|---|---|---|---|---|
| `Accessing member [...]` (float member) | 45 | **0** | 2 | 43 refused as designed -- bytes cannot model a float either, so the fallback deliberately does not fire |
| `Taking the address of a multi-byte member` | 60 | **8 (13%)** | 59 | the retry fires almost always, but the task then hits something else |
| **total** | **105** | **8 (7.6%)** | 61 | |

Where the 52 non-building addr-of tasks go: **28** `Could not handle left-hand side of assignment`
(the item-4 residue), **11** `Unsupported initializer for ...`, **12 OUT OF MEMORY**, 1 timeout.

⚠️ **The OOMs are real, not a local artifact.** They persist at `-Xmx14g`, so it is the container
limit doing the killing -- and this host's cgroup is 8 GB while `theta27-parse.xml` sets
`memlimit="7 GB"`, i.e. the benchmark is *tighter*. Byte-granular memory turns every wide access into
8 cells plus a Concat, and on the large intel-tdx / ldv-linux files that does not fit. Expect run 98
to show this family partly converting to OOM rather than to verdicts.

**Extrapolated yield of the fallback: ~55 of 724 tasks (~8%)**, essentially all from the addr-of
half. The fallback is correct and safe -- no wrong answers, floats refused loudly -- but it is not
the 1,448-run win the raw error count suggested. What actually blocks that family is the
`Could not handle left-hand side` work and the memory cost of the bytes model, in that order.

## Run 96 (parse-only) RESULT -- finished 2026-08-20, vs run 94

Both runs re-counted locally with one script so the comparison is like-for-like (the older
"31,984 built OK" figure in this file is in a different unit -- it is roughly half of the run count).
72,103 runs and 30,412 distinct tasks in each.

| | run 94 | run 96 | delta |
|---|---|---|---|
| built OK (`unknown`) | 63,055 | **63,385** | **+330** |
| error (total) | 9,048 | 8,718 | -330 |
| ERROR frontend, before parsing | 2,982 | 2,850 | -132 |
| ERROR frontend, after parsing | 1,518 | **1,070** | **-448** |
| OUT OF MEMORY | 3,358 | 3,572 | **+214** |
| TIMEOUT | 1,190 | 1,226 | +36 |

Frontend errors fell by **580**; ~250 of that is given back as OOM/TIMEOUT, netting +330 built OK.
The OOM rise is consistent with tasks now getting *further* before failing (a parse that used to die
early now proceeds and runs out of memory) but that is an interpretation, not a measurement. Neither
OOM nor ERROR scores anything, so no verdict was lost either way.

**Per-family, the targeted fixes landed exactly where they were aimed:**

| family | run 94 | run 96 | |
|---|---|---|---|
| item 7 compound bitwise `\|=` | 40 | **0** | gone |
| item 8 `Array with unspecified size` | 112 | **0** | gone |
| item 9 `ClassCastException` | 298 | **73** | -225; the residue advances to other failures |
| item 6 inlining arity | 172 | 112 | -60 |
| item 4/10 `Could not handle left-hand side` | 202 | **224** | **+22 -- newly EXPOSED**, not caused: tasks that used to die earlier now reach it |
| byte-addressed union (both messages) | 1,448 | 1,448 | unchanged **as expected** -- run 96 is the build BEFORE the fallback (`08b9ce772c`); this family is what run 98 tests |

The unchanged 1,448 is the useful control: it confirms the family is untouched by items 1-10 and is
entirely down to the fallback, which only run 98 carries.

## Runs 96 (parse, LOW) and 97 (portfolio, IDLE) -- launched 2026-08-20 09:55, benchcloud

Both from the SAME build: tool dir `Theta-svcomp-96` = HEAD `08b9ce772c` (batch-92 items 1-10 plus
the fp<->bits round-trip fix `f470a74ddf`). Gated 262 canaries / 69 fixtures / 0 FAIL before upload.

| run | XML | priority | screen | outdir |
|---|---|---|---|---|
| 96 parse-only | `xmls/theta27-parse.xml` | **LOW** | `theta-parse96` | `results/Theta-svcomp-96/theta27-parse.xml/2026-08-20_09:55:21/` |
| ~~97 portfolio~~ | `xmls/theta27-long900.xml` | IDLE | ~~`theta-portfolio97`~~ | **STOPPED 11:30 after 1h35m with 0 results** (IDLE, and parse96 at LOW held the queue) -- nothing lost |
| **98 portfolio** | `xmls/theta27-long900.xml` | **IDLE** | `theta-portfolio98` | `results/Theta-svcomp-98/theta27-long900.xml/2026-08-20_11:32:07/` |

Run 97 was replaced by **run 98** on a newer build, at the user's direction: tool dir
`Theta-svcomp-98` = HEAD `e07b3354df`, which adds the bytes-memory-model fallback with floats
refused loudly under it (`ByteMemoryPass`). The **parse run 96 was deliberately left running on the
older build** (`Theta-svcomp-96` = `08b9ce772c`), so its comparison against run 94 measures items
1-10 only, without the fallback. Run 98's tool dir is separate precisely so run 96's files are not
disturbed mid-flight. Launch checks on 98: 0 `Cannot start process`, 0 `OutOfMemoryError`.

Both pinned `--vcloudCPUModel Skylake --vcloudClientHeap 8192`. Launch sanity checks passed on both:
0 `Cannot start process`, 0 `OutOfMemoryError`, results accumulating, screens alive.

⚠️ **PORTFOLIO CHANGED, and it confounds the run-93 comparison.** `xmls/theta27-long900.xml` passed
`--portfolio STABLE`, and `STABLE` maps to **complex26** (`ConfigToPortfolio.kt`), not complex27 --
so every previous "SV-COMP 27" portfolio run, run 93 included, was actually run on the 2026
portfolio. It now passes `--portfolio COMPLEX27` (backup at `xmls/theta27-long900.xml.stable-bak`).
COMPLEX27 is also the only portfolio aware of the byte-addressed memory model. Smoke-tested on three
canary tasks with known verdicts before launch; COMPLEX27 and STABLE agreed on all three.

Consequence for triage: a verdict that differs from run 93 is **portfolio AND fixes**, not fixes
alone. To attribute a regression to this batch's code, re-run that task under both portfolios rather
than assuming. Baselines: run 94 parse = 31,984 built OK / 1,492 frontend-before / 850
frontend-after; run 93 portfolio = score 19,804, 57 wrong, 18 missed bugs (on complex26).

### Item 10 follow-up: the fp<->bits round trip IS fixed (2026-08-20, commit f470a74ddf)

User-directed: "attempt to fix the fp-bits roundtrip; if not possible, just fail on the fpToIeeeBv
when bytes model is used." Both halves are now true.

**The cause was not `fpToIEEEBV` being wrong.** `ByteMemoryPass.wide()` accepted only `BvType`, so a
floating-point cell was left in an array of its own while everything else was split into byte cells.
A `double` and the bytes overlapping it were therefore unrelated storage -- the bytes were never
written at all, so a read of them was unconstrained. Extending the split to `FpType` (store
`fpToIEEEBV(v)`, rebuild with `fpFromIEEEBV`, NaN pinned to the canonical quiet encoding that
FrontendXcfaBuilder already used for the same reason, now shared via `FpUtils.canonicalNaNBits`)
makes all four punning cases answer Safe where they answered Unsafe, and NaN survives the trip
(`x != x` still holds, exponent still all ones). Every expectation came from gcc.

**Where it cannot be done, it now fails loudly** -- the requested fallback. `fp.to_ieee_bv` is a Z3
extension; checked directly against the shipped MathSAT binary, it is an "unknown symbol" there,
while the from-bits direction `((_ to_fp eb sb) bv)` IS standard and accepted. GenericSmtLibExprTransformer
already throws `UnsupportedOperationException` for the to-bits direction, which is the right outcome.

**The automatic fallback still does NOT ship.** Re-applied and re-measured after the round-trip fix:
float-newlib tasks build (210 -> 0) but then die in the backend on that same unsupported operation,
because complex27 runs BMC-MathSAT first for byte-addressed memory. Score 0 either way, so there is
no gain to bank -- and `bytes` remains opt-in, so nothing changes by default. Making it pay off needs
a to-bits encoding MathSAT can solve, which is the open piece.

### Item 10: why the bytes fallback is not shipped (measured 2026-08-19)

**The fallback itself was built and works.** `RequiresByteAddressedMemoryException` raised at the two
union refusal sites (`ExpressionVisitor:1208` address-of-multi-byte-member, `:2607`
byte-laid-out-member), an escape hatch in `getXcfa` beside the existing `rethrowPointerSplitLimitation`
(needed because `getXcfa` catches `Exception` and calls `exitProcess`, so a caller cannot simply wrap
it in a `try` -- that is why the first attempt silently did nothing), and a retry in
`ExecuteConfig.frontend` pinning `memoryModel = bytes` + `arithmetic = bitvector`. Measured:

| | exit |
|---|---|
| `float-newlib/double_req_bl_{0210,0220a,0240a}` before | 210, `byte-addressed union` |
| same, with the fallback | **0** |
| explicit `--memory-model multi` / `flat` / `--arithmetic integer` | 210, no fallback (user choice respected) |

**Why it was reverted.** The bytes model gives WRONG ANSWERS on double/bytes punning -- the exact
pattern that triggers the fallback:

    u.value = 1.0;
    if (u.parts.msw != 0x3FF00000u) reach_error();   // gcc: unreachable. theta: SafetyResult Unsafe

That is with `--memory-model bytes --arithmetic bitvector` passed *explicitly*, no fallback involved,
so the unsoundness is pre-existing in the model and not something the fallback introduces. The union's
own layout is fine (`u.words[1] == u.parts.msw` verifies Safe); it is specifically the bits of a
double **written as a double** that come back unconstrained, which yields spurious counterexamples.

The connection is not incidental: the cell models refuse this program *because* the fp<->bits round
trip is unsound (the batch-59 NaN gate on `fpToIEEEBV`). The byte-addressed model does not fix that
round trip, it merely does not check. So the refusal I was converting into a fallback trigger is a
load-bearing refusal.

**Scale of the averted damage:** the two union messages are the largest frontend error family in run
94 (1,448 runs: 852 address-of, 596 member-access). The half that the fallback actually rescues is
float-newlib 530 + float-benchs 24, all of which are this punning pattern. Turning ~554 ERRORs
(score 0) into wrong `false` verdicts costs -16 apiece. The intel-tdx half (688 runs) falls back but
then dies on a later unrelated limitation, so it gains nothing either.

**To make this shippable:** fix the fp<->bytes encoding under the byte-addressed model, then re-apply
the fallback -- the wiring is straightforward and is described above. Until then a loud ERROR is the
correct behaviour.

### Follow-up found while doing item 7 (NOT in the 10-item plan)

**Two of three arguments are dropped before inlining.** With the encoding fixed, the three
`coreutils-v9.5-units/relpath_*` tasks get past `|=` and now fail later:

    Inlining 'buffer_or_output': the call site supplies 2 argument(s) [(Bv 1), (Bv 32)]
    but the procedure has 4 parameter(s) [(buffer_or_output_ret, OUT), (::str, IN), (::pbuf, IN), (::plen, IN)]

The C is `static _Bool buffer_or_output (char const *str, char **pbuf, size_t *plen)` and every one
of its six call sites passes three arguments (`buffer_or_output ("..", &buf, &len)`). The `(Bv 1)` is
the `_Bool` return slot, so the call arrives with the slot plus exactly ONE real argument: two are
lost somewhere between the call expression and the inliner. This is NOT the item-6 shape (that is a
*void* callee with one slot too many, and the guard correctly declines to drop a non-void one), and
it is not caused by the encoding change -- it was merely hidden behind the `|=` failure. The two
survivors/casualties still need identifying; the `&buf`/`&len` address-of arguments are the
suspects, being the ones that differ from the surviving string literal.


**Then:** parse-only benchmark; if significantly better than run 94, a full portfolio run.
