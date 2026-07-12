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

### ⚠️ STILL OPEN: an abs-style bound does not constrain a later multiplication (false alarm)
The 8 `int64_t_rand_square_*_good` tasks are **still wrong** after the short-circuit fix, for an unrelated and **pre-existing** reason. Reduced, with no call and no floating point:

```c
if (a > -3037000500LL && (a < 0 ? -a : a) <= 3037000499LL) { long long r = a * a; }   // reports Unsafe; is Safe
if (a <= 3037000499LL && a >= -3037000499LL)               { long long r = a * a; }   // correctly Safe
```

Two *linear* bounds prove `a * a` in range; the same bound expressed through the abs idiom (`Ite(a < 0, -a, a) <= K`) does not, and the analysis reports an overflow. It is not the nonlinearity (the linear-bound version proves it), not the short-circuit, and not `imaxabs` (the ternary reproduces it without any call — and `abs` is modelled as exactly this `Ite`). Next step: dump the counterexample and see which `a` it claims, and whether the reported overflow is on `a * a` or on the `-a` inside the `Ite` (whose short-circuit wrapper may not be doing what it looks like it does).

## NEXT UP (queue as of batch 10; the in-flight benchmark run will re-rank it)

1. **N3 division overflow** (Phase 5.1) — **the top remaining no-overflow blocker**, and small. `OverflowDetectionPass.kt:240` throws `UnsupportedOperationException("We cannot soundly detect overflows with divisions.")` if the program contains **any** `DivExpr` *anywhere* — even though `DivExpr` is already in the pass's filter and `bvOverflowCondition` handles it. It was 15/60 (~25%) of the remaining errors in the no-overflow sample and matches the original triage's "division 831". Division overflows on exactly one input pair (`INT_MIN / -1`), so the integer path needs the same explicit condition the bitvector path already has — minding that C's `/` lowers to the `createIntDiv` Ite shape. Signed-shift overflow is still unchecked in **both** modes (also Phase 5).
2. **Phase 4 / AD6 grammar — the typedef-name ambiguity.** Highest-value frontend item left (`ParseCancellationException` ≈ 4,108 tasks, and still what blocks most of aws-c-common). Batch 6 found the concrete shape: with no symbol table and `typedefName : Identifier`, **`void *malloc(size_t);` is not parsed as a function at all** — it becomes two *variables*, `malloc` and `size_t`. Any function declared with a bare typedef'd parameter is misparsed the same way; `malloc` is merely special-cased now. Needs the resolved AD6 approach (typedef feedback + semantic predicate) and the "handle with care" protocol.
3. **"Pointer arithmetic not supported"** (`FrontendXcfaBuilder`) — now the *only* forced-bitvector crash class left, and it appears in the plain canary corpus (`loops/array-{1,2}.c`).
4. **N5 termination + recursion → graceful unknown**, and **D7 portfolio continues after a clean unknown** — both small, both mostly convert noise into unknowns.
5. **AD7 unions, bit-exact punning** across differently-typed members (currently rejected loudly rather than answered unsoundly) — architectural, needs the flat object layout.
6. **W5** `PRED_CART-BW_BIN_ITP-Z3` false `valid-deref` cluster (needs live debugging), **N7** Newton `MemoryAssignStmt`, **N6** `pthread_detach`, **C1** east-const.
7. **Capability/performance** (the timeout mass) — deliberately last: the profiles are only meaningful once the crash noise is gone.

**→ A full re-test is warranted now.** Expected: the largest frontend-error classes ("Only variable-backed functions" 1,543; asm NPE 882; unions 1,722 partially; alloca 421) should shrink; watch for new *wrong* results from fptr dispatch (candidate-set over-approximation), asm output havocing, and union offset-0 aliasing.

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
