# Possible issues found while documenting Theta modules

*Not yet reviewed by developers!*

## xsts-cli (git-history finding, 2026-07-10)

- [ ] **Lost feature: the CEGAR "stuck check" (divergence monitor) in xsts-cli.** Originally added
  2021-09 (`25239b882`, `ArgCexCheckHandler` + `--no-stuck-check`, on by default). PR **#188**
  "Progress check partial refactor" (merged 2023-04-25) replaced the old mechanism with
  `CexMonitor`/`MonitorCheckpoint` but wired it **only into xcfa-cli**; in XstsCli it kept the
  flags (`--check-arg`, `--no-cex-check`) and left the wiring commented out with
  `// TODO replace with new classes` — the PR description says "Mitigation is temporary
  unavailable". That TODO was never picked up; PR **#292** "Xsts cli clikt" (merged 2024-08-09,
  `33b824064`) silently deleted the commented block and the flags with the old file — **no
  discussion of the feature in either PR's review thread** (checked 2026-07-10).
  **Restore**: register a `CexMonitor` on `"CegarChecker.unsafeARG"` in xsts-cli's cegar command
  (mirror `xcfa-cli/ConfigToCegarChecker.kt:169`), catch `NotSolvableException`, re-add an
  opt-out flag. Same likely applies to cfa-cli/sts-cli (not verified).

## common/analysis (full audit 2026-07-09; spot-claims re-verified by grep)

### Likely genuine bugs / broken paths

- [ ] **`algorithm/mcm/analysis/FiniteStateChecker.check()` always returns unsafe** — the actual
  `PartialSolver` invocation is commented out (line ~76); a WiP stub shaped like a working
  `SafetyChecker`. Zero external consumers, so latent.
- [ ] **`algorithm/mdd/MddChecker` trace extraction**: on its hard `traceTimeout` (default 10s) it
  silently returns a degenerate-but-valid `Trace.of([ExplState.top()], [])` — callers get a
  meaningless counterexample instead of an error.
- [ ] **`tracegeneration`: `getFullTraces=true` is reachable but broken** — implementation
  commented out behind `assert !getFullTraces`, yet exposed via
  `xsts-analysis/XstsTracegenBuilder.setGetFullTraces(true)`.
- [ ] **`bounded/pipeline/PrimeMEPassValidator`** — the violation `throw` is commented out,
  downgraded to `System.err.println`: prime-count violations by passes go unenforced.
- [ ] **`expr/refinement/ItpRefutation`** — "not all-True" guard is `assert`-only; with `-ea` off,
  an all-True sequence yields `pruneIndex == size` → out-of-bounds in `ArgTrace.node(pruneIndex)`.
- [ ] **`zone/BasicDbm.hashCode()/equals()`** and **`zone/DBM.isSatisfied(ClockConstr)`** — 
  `UnsupportedOperationException("TODO")` stubs; safe only while nothing calls them.
- [ ] **`algorithm/ic3/Ic3Checker.tryBlock`** — author-flagged off-by-one uncertainty in the
  former-frames optimization: comment `"lehet, hogy 1, vagy 2??"`.
- [ ] **`algorithm/oc/OcTypes.kt`: `Event.clkSize`** — static mutable counter incremented in every
  Event ctor; global state across checker instances, corrupts IDL array sizing if not reset.
- [ ] **`algorithm/asg/ASGTrace`** — lasso-shape invariant checks commented out (with TODO) to
  accommodate `HackyAsgTrace`; malformed lassos are no longer caught at construction.
- [ ] **`algorithm/tracegeneration/summary/ExprSummaryFwBinItpChecker.kt`** — declares package
  `...expr.refinement` while living under `tracegeneration/summary/` (package/dir mismatch).

### Abstraction boundaries

- [ ] **`algorithm/mdd` exposes the external delta library through its public API** — e.g.
  `MddProof.getMdd()` returns `hu.bme.mit.delta`'s `MddHandle`, and delta types
  (`MddNode`, `MddVariable`, `IntObjMapView`, …) appear in signatures across the package.
  Consumers (xcfa-cli, xsts-cli, petrinet-analysis) must import delta directly; a delta
  upgrade ripples outward. Consider an adapter type if delta is ever swapped/upgraded.

### Unbounded static caches (leaks in long-running/portfolio processes)

- [ ] `algorithm/arg/ArgStructuralEquality` — static hash cache, never evicted.
- [ ] `utils/MddNodeVisualizer`/`MddHandleVisualizer`/`MddNodeCacheVisualizer` — static
  `IdentityHashMap` id registries, never cleared.

### Dead / orphaned code candidates (grep-verified zero consumers)

- [ ] `expr/ExprMeetStrategy` enum + `SemanticExprMeetStrategy`/`SyntacticExprMeetStrategy`
  (enum wired to nothing); `IndexedExprState` family (self-contained, no external consumers);
  `ExprTraceCombinedChecker`/`ExprTraceStatusMergers` (only their own factories).
- [ ] `arg/ArgNode.disableCoveringAbility()`/`canCover` — zero callers.
- [ ] `prod2/prod3/` and `prod2/prod4/` packages — zero consumers, zero tests.
- [ ] `mdd/fixedpoint/Cursor*Provider`s — implemented but not selectable via `IterationStrategy`;
  only a petrinet test touches them.
- [ ] `ptr/`: `PtrPrec.smth` field, `PtrTracking` enum, `TopCollection` — unreferenced.
- [ ] `algorithm/arg/ArgChecker.isUnwinding` — `UnsupportedOperationException` stub.
- [ ] `prod2/Prod2ExplPredStrengtheningOperator.strengthen` — computes a `removed` set it never uses.

### Build / structure

- [ ] **`build.gradle.kts` dependency audit**: `Deps.delta` → `algorithm/mdd` (justified);
  `graph-solver` → `mcm` (justified); `javasmt` → only `UserPropagatorOcChecker.kt` (justified);
  **`solver-z3-legacy`: zero `src/main` imports, declared twice** — likely removable;
  **`Deps.hoaf`: unused here** (only `common/ltl` uses jhoafparser) — likely removable.
- [ ] **Dual source roots**: `multi/` splits between `src/main/java/` and `src/main/kotlin/` —
  consider consolidating.
- [ ] `algorithm/arg/ARG.initialized` — public mutable field as cross-class protocol (also set by
  `ArgAdapterHelper.kt` and `MddExpressionRepresentation`, not just `ArgBuilder`).
- [ ] `multi/builder/MultiBuilderResult.kt` — documented dead code kept as a Kotlin-plugin-crash
  workaround next to the real `MultiBuilderResultPOJO.java`; trap for cleanup attempts.
- [ ] Naming collision: `algorithm/oc/OcTypes.kt` defines `Relation<E>` unrelated to core's
  CHC `Relation` — grep hazard.

# `common/core` (2026-07-08)

Found during code-derived doc generation (six-agent audit of all core packages; each claim
re-verified by direct read/grep before listing). **Not fixed — pending human triage.**
Delete entries as they're resolved or judged intentional.

## Likely genuine bugs

- [ ] **`VarChangerUtils.kt` — runtime `TODO()`**: the `Stmt.changeVars` `when` has an
  `else -> TODO("Not yet implemented")` branch; hitting it (e.g. `MemoryAssignStmt`, `OrtStmt`)
  throws `NotImplementedError` at runtime. Backs the public `StmtUtils.changeVars`.
- [ ] **`clock/constr/AndConstr`** — construction `AssertionError` on a bare `FalseConstr`
  operand (`toAtomicConstrs` special-cases `TrueConstr` but not `FalseConstr`).
- [ ] **`fptype/FpLitExpr.compareTo(FpType)`** — stub, always returns 0; odd signature too
  (compares against a `FpType`, not another `FpLitExpr`).
- [ ] **`type/anytype/InvalidLitExpr.equals`** — returns `false` unconditionally (non-reflexive),
  no `hashCode` override. *Possibly intentional* NaN-like semantics ("invalid equals nothing,
  not even itself") — but there is no comment saying so, the missing `hashCode` makes it
  hazardous in hash-based collections either way, and it also skips the family's
  `getHashSeed()`/`getOperatorLabel()` contract. At minimum deserves a documenting comment.

## Confirmed inconsistencies / traps (may be intentional — deserve a comment)

- [ ] **Operator-label collisions** break toString/DSL round-trips:
  `"="` = both `FpEqExpr` (IEEE fp.eq, NaN≠NaN) and `FpAssignExpr` (bit-identity);
  `"bvpos"` = both `BvPosExpr` (identity) and `BvSignChangeExpr` (type-reinterpreting).
- [ ] **`functype/FuncType.getDomainSize()`** throws `UnsupportedOperationException` — any
  generic code iterating `Type.getDomainSize()` crashes on func-typed decls.
- [ ] **`functype/FuncAppExpr.eval()`** — unimplemented stub ("TODO Auto-generated method stub").
- [ ] **`utils/TypeUtils.checkAllTypesEqual(Expr<?>)`** (single-arg overload) — no-op beyond
  null-check; misleading name vs. its 2-arg/n-ary siblings which actually compare.
- [ ] **`utils/BvUtils.fitBigIntegerIntoSignedDomain`** — carries an author comment
  `// TODO: is this correct? See modifications below in unsigned`.
- [ ] **`ClockOps.fromStmt`** — `AssumeStmt` case rethrows a bare `IllegalArgumentException()`
  with no message/cause, discarding the original diagnostic; `ClockConstrs.formExpr` failures
  (e.g. fractional bounds, `denom != 1`) are likewise message-less.

## Dead-code candidates

- [ ] **`utils/VarPoolUtil`** — only production call site is commented out
  (`StmtToExprTransformer.java:153,191`); otherwise test-only. Abandoned nondet-temp-var scheme?
- [ ] **`utils/Lens`** — zero consumers repo-wide; `xta-analysis` has its own unrelated
  same-named interface instead.
- [ ] **`parser/` (CoreParser/CoreInterpreter Lisp stack)** — no non-test consumers found;
  supports only skip/assign/assume/havoc. Parallel to (and older than) `dsl/`.

## Stale docs

- [ ] **`type/inttype/package-info.java`** — claims int literals are "long in the
  implementation"; they are `BigInteger` (unbounded).
- [ ] **`stmt` reachability**: composite stmts (`Sequence`/`NonDet`/`Ort`/`Loop`/`If`) and
  `MemoryAssignStmt` are unreachable from every text format (CoreDsl grammar + Lisp parser
  alike) — likely intentional (analysis-internal constructs), but nothing says so.

## Style-only

- [ ] `MemoryAssignStmt` uses Guava `Objects.hashCode`/`equal` instead of the codebase's
  `HASH_SEED` + cached-volatile pattern; `IfStmt` is the only non-`final` Stmt class.
- [ ] `FpIsNanExpr`/`FpIsInfiniteExpr.with(...)` use raw types (unchecked), unlike all siblings.
- [ ] `functype/` and `enumtype/` lack `package-info.java` (all sibling families have one).
