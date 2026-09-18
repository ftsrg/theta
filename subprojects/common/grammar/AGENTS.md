# common/grammar — notes for editing this module

Gradle module: `:theta-grammar`. Kotlin + ANTLR (grammars in [src/main/antlr/](src/main/antlr/): `CommonTokens.g4`, `Type.g4`, `Expr.g4`, `Stmt.g4`, `Declarations.g4`).

**What this module is**: the parser for core's own `toString()` output. Core exprs/stmts/types print in lisp style (`Utils.lispStringBuilder`); this module parses that text back into core objects — verified round-trip in [ExprTest](src/test/java/hu/bme/mit/theta/grammar/dsl/ExprTest.kt)/[StmtTest](src/test/java/hu/bme/mit/theta/grammar/dsl/StmtTest.kt) (`assertEquals(serialized, expr.toString())`, then re-parse). Plus Gson adapters for JSON-serializing analysis objects (ARG, Trace, SafetyResult).

Of the repo's three text stacks for core objects, this is the **machine round-trip** one: `core/dsl` (CoreDslManager) is for human-written models, `core/parser` is legacy Lisp with no production consumers, and this module is what xcfa uses to persist/restore models and results.

## Invariants

1. **The grammar must track core's `toString()` exactly.** A new expr class (or a changed `OPERATOR_LABEL`) in core silently breaks the round-trip until `Expr.g4` + [ExprParser.kt](src/main/java/hu/bme/mit/theta/grammar/dsl/expr/ExprParser.kt)'s `ExprCreatorVisitor` learn it — there is no compile-time coupling. The round-trip tests are the only guard; extend them with every grammar change.
2. **`Expr.g4` is full-fidelity** (~45 rules: quantifiers, ite, arrays, bv, fp, deref, func lits). **`Stmt.g4` is not**: skip/assign/**memAssign**/havoc/assume + `;`-separated `stmtList` only — no composite stmts (Sequence/NonDet/Loop/If/Ort as objects; xcfa doesn't need them since XCFA edges carry label lists).
3. Parsing is scope-dependent: wrappers take a `Scope` ([SimpleScope](src/main/java/hu/bme/mit/theta/grammar/dsl/SimpleScope.kt)) mapping names → `Decl` symbols, and instantiate against an `Env` — same `Decl`-identity rules as everywhere (names don't resurrect decls; the scope must hold the *original* instances).
4. The [gson/](src/main/java/hu/bme/mit/theta/grammar/gson/) adapters are registered in one place: `xcfa-cli/utils/GsonUtils.kt`. New adapter → register it there. `ArgAdapterHelper` reconstructs ARGs (and sets `ARG.initialized` directly).
5. ANTLR generated sources land under `build/` at build time — edit only the `.g4` files; parser/visitor base classes regenerate.

## Change recipes

- **Core gained a new expr/type**: add the rule to the `.g4`, a `visit...` override in the matching `*CreatorVisitor` (Expr/Type/Stmt `Parser.kt`), and a round-trip test case. Check the label matches core's `OPERATOR_LABEL` verbatim.
- **New serializable analysis object**: write a Gson `TypeAdapter` here (copy `TraceAdapter`), register in `GsonUtils.kt`.

## Files

- [dsl/](src/main/java/hu/bme/mit/theta/grammar/dsl/) — `ExpressionWrapper`/`StatementWrapper`/`TypeWrapper` (lazy: hold text + scope, `instantiate(env)` parses), `SimpleScope`, `Utils.kt` (`textWithWS`, `ThrowingErrorListener` — parse errors throw instead of printing).
- [gson/](src/main/java/hu/bme/mit/theta/grammar/gson/) — adapters for `Arg`, `Trace`, `SafetyResult`, states, `VarDecl`, pairs/triples/optionals; `StringTypeAdapter` funnels the wrapper classes through their text form.

Consumers: `xcfa/xcfa` (model round-trip), `xcfa-cli` (gson + wrappers). (`c-frontend`/`btor2-frontend` declare the dep but don't use it — see `possible-issues.md`.)
