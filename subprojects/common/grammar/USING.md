# Using theta-grammar — parsing core objects from text

Counterpart of [CLAUDE.md](CLAUDE.md). Use this module when you need to round-trip core exprs/stmts/types through text (e.g. persisting models or results). The text format **is** core's `toString()` output — you don't need a writer, `expr.toString()` is the writer.

```kotlin
implementation(project(":theta-grammar"))
```

```kotlin
// scope must hold the ORIGINAL Decl instances (Decl equality is identity!)
val symbolTable = SymbolTable()
decls.forEach { symbolTable.add(Symbol { it.name }) }   // see SimpleScope for the real pattern
val scope = SimpleScope(symbolTable)

val expr: Expr<out Type> = ExpressionWrapper(scope, exprText).instantiate(env)
val stmt: Stmt          = StatementWrapper(stmtText, scope).instantiate(env)
val type: Type          = TypeWrapper(typeText).instantiate()
```

- `Expr` coverage is full-fidelity (quantifiers, bv/fp/arrays, deref); `Stmt` covers only skip/assign/memAssign/havoc/assume (+ `;`-lists).
- Parse errors throw (`ThrowingErrorListener`) instead of printing to stderr.
- JSON for analysis objects (ARG/Trace/SafetyResult): the Gson adapters in [gson/](src/main/java/hu/bme/mit/theta/grammar/gson/), registered via `xcfa-cli`'s `GsonUtils.kt` — copy that registration if you serialize elsewhere.
- For *human-authored* model text, prefer `core/dsl`'s `CoreDslManager` instead — this module's format is machine-oriented.

Reference consumers: `xcfa/xcfa` model serialization, `xcfa-cli` (`GsonUtils.kt`). Round-trip examples: [ExprTest.kt](src/test/java/hu/bme/mit/theta/grammar/dsl/ExprTest.kt).
