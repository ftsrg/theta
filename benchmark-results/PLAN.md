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
