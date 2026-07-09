# Possible issues found while documenting Theta modules

## common/analysis (Phase A skim, 2026-07-09 — preliminary, fan-out pending)

- [ ] **`build.gradle.kts`** declares `solver-z3-legacy` twice (`implementation(project(...))` and
  `implementation(project(mapOf("path" to ...)))`); the "generic" analysis module also depends
  directly on `solver-javasmt`/`z3-legacy`/`graph-solver` — intentional?
- [ ] **`algorithm/arg/ARG.java`** — `public boolean initialized; // Set by ArgBuilder`:
  public mutable field as cross-class protocol.

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
