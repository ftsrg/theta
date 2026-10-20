# common/core — notes for editing this module

Gradle module: `:theta-core` — all modules are named `theta-<dirname>` (see [settings.gradle.kts](../../../settings.gradle.kts)); `:core:...` does **not** resolve.

- Build/tests: `./gradlew :theta-core:build` · `./gradlew :theta-core:test`
- Formatting (Spotless: google-java-format AOSP, ktfmt google style) is required but **not** run automatically: run `./gradlew spotlessApply` locally, or trigger via `\format` comment on the GitHub PR. Every file needs the copyright header ([doc/copyright-header.txt](../../../doc/copyright-header.txt)).
- Conceptual overview: [README.md](README.md) here; formalism-level docs in [doc/wiki/](../../../doc/wiki/).

Paths below are relative to [src/main/java/hu/bme/mit/theta/core/](src/main/java/hu/bme/mit/theta/core/).

## Vocabulary

| Concept | Where | What |
|---|---|---|
| `Type` | [type/Type.kt](src/main/java/hu/bme/mit/theta/core/type/Type.kt) | marker; `domainSize` (finite/`INFINITY`) |
| `Expr<T : Type>` | [type/Expr.kt](src/main/java/hu/bme/mit/theta/core/type/Expr.kt) | immutable AST node: `ops`/`withOps`/`map`/`eval(Valuation)`; **sealed** Kotlin hierarchy |
| `LitExpr<T>` | [type/LitExpr.kt](src/main/java/hu/bme/mit/theta/core/type/LitExpr.kt) | marker for literals (= evaluated exprs) |
| `Decl<T>` | [decl/](src/main/java/hu/bme/mit/theta/core/decl/) | named+typed declaration; `getRef()` gives its `RefExpr` |
| `ConstDecl`/`VarDecl`/`ParamDecl` | [decl/](src/main/java/hu/bme/mit/theta/core/decl/) | create **only** via [Decls](src/main/java/hu/bme/mit/theta/core/decl/Decls.java)`.Const/Var/Param` |
| `RefExpr<T>` | [type/RefExpr.kt](src/main/java/hu/bme/mit/theta/core/type/RefExpr.kt) | leaf expr referencing a `Decl` |
| `Valuation` | [model/](src/main/java/hu/bme/mit/theta/core/model/) | `Decl → LitExpr`; is-a `Substitution`; `toExpr()`, `isLeq()` |
| `Substitution` | [model/](src/main/java/hu/bme/mit/theta/core/model/) | `Decl → Expr`; `apply(expr)` rewrites refs recursively |

## Invariants — violating these breaks distant code

1. **Decls are identities, not values.** `Decl.equals` is `this == obj`. Two `Decls.Var("x", Int())` calls are two *different* variables. Never reconstruct a decl to "find" it — pass instances around.
2. **Exprs are immutable structural values.** `equals` compares ops; `hashCode` is lazily cached (`volatile int`, per-class `HASH_SEED`). The arity base classes implement both; new expr classes copy a sibling and override `equals` only for state beyond their ops. (A few classes deliberately bypass the arity base classes — see [type/AGENTS.md](src/main/java/hu/bme/mit/theta/core/type/AGENTS.md).)
3. **Simple types are singletons** — exactly `BoolType`, `IntType`, `RatType` (`IntType.getInstance()` = `IntExprs.Int()`); the rest (array, bv, fp, func, enum) are per-instance.
4. **Vars never reach solvers** — only constants do. `VarDecl` → per-index `IndexedConstDecl` (`_x:3`) via [utils/PathUtils.java](src/main/java/hu/bme/mit/theta/core/utils/PathUtils.java) `unfold/foldin/extractValuation` + `VarIndexing` ([utils/indexings/](src/main/java/hu/bme/mit/theta/core/utils/indexings/)). Any expr headed to SMT goes through this.
5. **Traceability wrappers are transparent.** [type/TraceableWrapperExpr.kt](src/main/java/hu/bme/mit/theta/core/type/TraceableWrapperExpr.kt) attaches a frontend's `TraceabilityInfo` (the C frontend: its `CComplexType`) to an expr; type, `eval`, `toString`, `equals`/`hashCode`, the solvers, `ExprWriter` and `ExprCanonizer` all see the wrapped expr. Matching on an expr class must look through it (`e.unwrapTraceable() is X`); `ExprSimplifier.simplify` strips, simplifies and rewraps the nodes it left unchanged, and a rewritten operand keeps what `TraceabilityInfo.afterRewrite` allows. A canonical `decl.ref` is never wrapped: its info is `VarDecl.traceability`. Analyses take wrapper-free input ([type/Traceability.kt](src/main/java/hu/bme/mit/theta/core/type/Traceability.kt) `stripTraceability`).
6. **Factory convention:** concrete exprs have a private ctor + companion `@JvmStatic` `of(...)` (typed) + `create(...)` (wildcard, uses [utils/TypeUtils.java](src/main/java/hu/bme/mit/theta/core/utils/TypeUtils.java)`.cast`). Human API is the family's `XExprs` class (`IntExprs.Add`, `BoolExprs.And`) or type-generic [abstracttype/AbstractExprs.java](src/main/java/hu/bme/mit/theta/core/type/abstracttype/AbstractExprs.java).
7. **Serializable model:** every concrete expr, stmt, decl and type class is `@Serializable`; its ctor params are its properties, and checks/normalization live in the factory (deserialization bypasses it). `Expr`, `Stmt`, `Decl` and the stateful types serialize as indices into an [serialization/ObjectTable.kt](src/main/java/hu/bme/mit/theta/core/serialization/ObjectTable.kt), which writes each object once with the serializer its class is listed with in [serialization/CoreTableClasses.kt](src/main/java/hu/bme/mit/theta/core/serialization/CoreTableClasses.kt): its generated one, which is `generatedSerializer()` (`@KeepGeneratedSerializer`) where the class itself names a reference serializer. The list is explicit so that no lookup needs reflection at runtime; `ObjectTableTest` fails while a class is missing from it. A body property with a backing field is serialized too, so caches need `@Transient`.

## The type-family pattern ([type/](src/main/java/hu/bme/mit/theta/core/type/)`<x>type/`)

Each family = `XType` + `XExprs` static factory in `<x>type/` (families: bool, int, rat, bv, fp, array, func, enum; [anytype/](src/main/java/hu/bme/mit/theta/core/type/anytype/) holds the type-generic `Exprs`), plus `XLitExpr` and operator exprs. The expressions themselves all live flat in package `hu.bme.mit.theta.core.type`: `Expr` is a sealed Kotlin hierarchy, and Kotlin requires every subtype of a sealed type to share its package. Expressions defined in other modules extend `ForeignExpr`/`ForeignLitExpr` instead (currently `UnsupportedInitializer`, `LabelExpr`, `MallocLitExpr`).

Cross-family operations are traits in [type/abstracttype/](src/main/java/hu/bme/mit/theta/core/type/abstracttype/) — `Additive`, `Multiplicative`, `Divisible`, `Equational`, `Ordered`, `Castable`. The *Type* implements the trait and is the factory for its operator exprs (`IntType implements Additive<IntType>`); `AbstractExprs` dispatches on runtime op types.

[SmartBoolExprs](src/main/java/hu/bme/mit/theta/core/type/booltype/SmartBoolExprs.java) constructors simplify locally (`And([x])` → `x`); `BoolExprs` constructs verbatim.

## Change recipes (verified against git history)

**New operator on an existing family:** add the expr class to `type/` (copy the nearest sibling `.kt`), list it in `serialization/CoreTableClasses.kt`, register in `XExprs`, teach [utils/ExprSimplifier.java](src/main/java/hu/bme/mit/theta/core/utils/ExprSimplifier.java) — one `addCase(NewExpr.class, this::simplifyNew)` in its `DispatchTable2` + handler (default falls through to plain recursion; cf. 70765f8fc) — and, if it must reach SMT, the solver transformers below. Full family conventions + per-family deviations: [type/AGENTS.md](src/main/java/hu/bme/mit/theta/core/type/AGENTS.md).

**New Stmt:** add the class in [stmt/](src/main/java/hu/bme/mit/theta/core/stmt/) (`@Serializable`, private ctor + `of`, copy a sibling, listed in `CoreTableClasses` like a new expr; `Stmt` is sealed, so it must stay in that package — statements from other modules extend `ForeignStmt`), add `visit(...)` to `StmtVisitor` — it has no defaults, so **the compiler enumerates every implementor that must be updated** (currently 10, all in core: `ClockOps`, `StmtWriter`, `SpState`, `WpState`, `StmtSimplifier`, `StmtToExprTransformer`, `StmtAtomCollector`, `StmtCounterVisitor`, `VarCollectorStmtVisitor`, `WrittenVarCollectorStmtVisitor`). Note several implementors only support the atomic stmts (Skip/Assume/Assign/Havoc) and throw on the rest — decide per implementor whether your stmt needs real support. Optionally add a `Stmts` factory method (`Ort`/`Loop`/`If` don't have one — use their `.of()`), and extend `CoreDsl.g4` + `dsl/impl/StmtCreatorVisitor` only if it must be parseable from text.

**New type family** (evidence: EnumType, cf9f52487 + follow-ups): `core/type/<x>type/*` (type + factory) and its exprs in `core/type/` → `ExprSimplifier` → [type/DomainSize.java](src/main/java/hu/bme/mit/theta/core/type/DomainSize.java) if needed → **all four solver stacks** — [solver-z3](../../solver/solver-z3/), [solver-z3-legacy](../../solver/solver-z3-legacy/), [solver-javasmt](../../solver/solver-javasmt/), [solver-smtlib](../../solver/solver-smtlib/) — each has `{Expr,Term,Type}Transformer` (+ `Solver`, and smtlib may need a strategy class, cf. `SmtLibEnumStrategy`) → the consuming formalism's DSL + tests (xsts in that commit).

## Rest of core (verified summaries)

- [stmt/](src/main/java/hu/bme/mit/theta/core/stmt/) — Stmt taxonomy: atomic `Skip`/`Assume`/`Assign`/`MemoryAssign`/`Havoc` + composite `Sequence`/`NonDet`/`Ort`/`Loop`/`If`. Only the atomics are reachable from text (`core/dsl` parses assign/assume/havoc; `common/grammar` additionally memAssign/skip); composites are Java-only. `NonDet`/`Ort`/`Sequence` silently coerce an empty list to `[Skip]`. `MemoryAssignStmt.tracedDeref` is the target as given (possibly a wrapped dereference); `deref` is always the bare `Dereference`.
- [utils/](src/main/java/hu/bme/mit/theta/core/utils/) — public surface: `ExprUtils`, `StmtUtils`, `TypeUtils`, `PathUtils`; the rest are package-private helpers behind them. `StmtToExprTransformer` does the SSA-style unfolding (If/NonDet via join-and-equate on `VarIndexing`; `Loop`/`Ort` unsupported — unroll first). `WpState`/`SpState` support only atomic stmts. `ExprCanonizer` normalizes comparisons to `<`/`=`/`Not` and sorts commutative ops by hashCode; `ExprCnfTransformer` = Tseitin equisat CNF (`__CNF<n>` fresh vars); `ExprCloser` closes free vars into `ParamDecl`s.
- [clock/](src/main/java/hu/bme/mit/theta/core/clock/) — a **parallel IR**, not a type family: `ClockConstr`/`ClockOp` don't implement `Expr`, they lower via `toExpr()`/`toStmt()` and have their own visitors. Integer-bound constraints over `VarDecl<RatType>` clocks, for DBM/zone analysis (`common/analysis` zone/, `xta`). `ClockConstrs.formExpr`/`ClockOps.fromStmt` are lossy reverse-parsers accepting only specific shapes (integer bounds, `x ⋈ c` / `x−y ⋈ c`).
- [dsl/](src/main/java/hu/bme/mit/theta/core/dsl/) — `CoreDslManager` parses/writes types, exprs, and atomic stmts from text (`declare(decl)` first, then `parseExpr`/`parseStmt`); grammar in [src/main/antlr/](src/main/antlr/) `CoreDsl.g4`. [parser/](src/main/java/hu/bme/mit/theta/core/parser/) is a separate legacy Lisp-S-expression stack (`CoreParser`/`CoreInterpreter`, no non-test consumers found).
