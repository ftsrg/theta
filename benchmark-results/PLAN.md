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

Not yet started (batch 2): C3 builtins, C1 east-const + GlobalDeclUsageVisitor hardening, N7 Newton MemoryAssignStmt, N6 pthread_detach, Phase 1.5 memsafety scope lifetimes, Phase 4 grammar, Phase 6 architectural. (OC / `&expr` remain out of scope — separate PRs.)

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
04-mutex) persist and are **out of scope** (separate PR).

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
the folding introduced by `35dde5041` is defeating that threading. **Open — needs a focused look at
how the unguarded-operand folding interacts with `OverflowDetectionPass`, not another predicate tweak.**

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

**DEFERRED (user decision, batch 25): the `psyco_math_1` soundness regression stays open for now.**
One wrong result (no-overflow, correct→wrong) from `35dde5041`; net branch state is +2989 correct so
it is accepted for the moment. Full root cause + the two failed fix attempts are in **batch 25** above.
Fix, when picked up, is at the expression level (`OverflowDetectionPass` short-circuit threading), not a
`mustNotRunUnconditionally` predicate tweak, and must not revert `35dde5041` or `89020cef2`.

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

### W6. OC (ordering-consistency) multithreaded checker false positives (2 tasks) — OUT OF SCOPE: separate PR
`pthread/singleton.yml` (memsafety, expected true → got false(unreach-call), **"Unsafe, Trace length: 0"**), `goblint-regression/04-mutex_17-ps_add1_nr.yml` (no-overflow, expected true → got false, trace length 20).
- Findings for reference only (OC issues are being resolved in a separate PR — **do not fix here to avoid double-fixing**): `XcfaOcChecker.kt:131-146` swallows trace-extraction exceptions and still reports `SafetyResult.unsafe(EmptyCex, ...)`; forced 2-iteration loop unroll (`XcfaOcChecker.kt:60-70`) has a Safe-only reliability downgrade (`ExecuteConfig.kt:300-315`), never Unsafe; MULTITHREAD portfolio dispatches OC on memsafety/overflow-lowered `ERROR_LOCATION` properties (`MemsafetyPass.kt:82`, `multithread.kt:210-285`).
- **This plan's only action**: keep these 2 tasks in the wrong-result guard set (Phase 0) so the external OC PR's effect is verified by the rerun; no OC code is touched by this plan.

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

(W6 / OC items intentionally absent — separate PR.)

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
5. **Wrong-result guard set** after every phase (13 wrong + neighbors): zero wrong verdicts tolerated (the 2 OC tasks tracked for the external PR's effect).
6. **Final**: one full benchmark re-run (same infra as this run) after Phases 1-5; success criteria: wrong ≤ 4 (W5-class if unresolved + OC pending external PR), frontend-failure errors < 5,000 (from 17,570), no new wrong results, correct > 7,500 (from 5,917; conservative — Juliet/no-overflow/memcleanup alone should add ~1,000).

## 5. Architectural-decision register
Resolved (per review, 2026-07-09):
| ID | Decision | Resolution |
|---|---|---|
| AD1 (W2/1.3) | Signed-cast wraparound under integer arithmetic | **Resolved**: new `FrontendConfig` option `--enable-signed-wraparound` enabling modular wraparound; default off (signed wraparound is UB pre-C23) |
| AD3, AD4 (OC) | OC Unsafe guarding / OC on lowered properties | **Removed from plan** — OC issues handled in a separate PR; only guard-set tracking here |
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
