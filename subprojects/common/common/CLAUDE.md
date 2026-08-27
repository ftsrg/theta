# common/common — notes for editing this module

Gradle module: `:theta-common`. Build/tests: `./gradlew :theta-common:build` / `:theta-common:test`. Formatting/copyright: see root [CLAUDE.md](../../../CLAUDE.md).

**Every other module depends on this one.** Public-API changes here ripple through the entire repo — prefer adding over changing signatures, and grep all of `subprojects/` before renaming anything.

## Invariants

1. **Deterministic collections.** [CollectionUtil](src/main/java/hu/bme/mit/theta/common/collection/CollectionUtil.java)`.createMap/createSet` return insertion-ordered (LinkedHash) collections via a global `CollectionFactory`. Core (`VarDecl`, `MutableValuation`, …) builds on these — iteration order affects state enumeration and thus reproducibility of whole verification runs. Don't swap in an unordered factory casually.
2. **`Logger.Level` is ordered** (DISABLE < RESULT < BENCHMARK < MAINSTEP < SUBSTEP < INFO < DETAIL < VERBOSE) and loggers filter by comparison — inserting a new level renumbers the ordering for every consumer.
3. **Tuples are fixed-arity value classes** (`Tuple1`..`Tuple7`, generic `TupleN`); structural equals/hashCode, no interning. `Unit`, `Either`, `Try` follow plain functional-value semantics.
4. **`dsl/` (Scope/Symbol/Env) is a public contract**: consumed by `common/core`'s DSL, `common/grammar`, `cfa`, and every `solver-*` module for symbol resolution. Changes here are effectively changes to all language frontends.
5. `visualization/Graph` is the neutral output format — algorithm code builds `Graph`s, and only `visualization/writer/` (`GraphvizWriter`, `JSONWriter`, `YedWriter`) knows concrete syntaxes. Keep it that way; don't emit dot strings from analysis code.

## Package map

- root — `Utils` (`lispStringBuilder`, `head`/`tail`, `singleElementOf`), `DispatchTable`/`DispatchTable2` (runtime type→handler dispatch, builder-based; the backbone of `ExprSimplifier` and `clock/`'s expr reduction), tuples, `Either`/`Try`/`Unit`, `IntMatrix`/`GrowingIntArray` (used by zone DBMs), `OsHelper`, `CliUtils`.
- [logging/](src/main/java/hu/bme/mit/theta/common/logging/) — `Logger` iface + `ConsoleLogger`, `FileLogger`, `NullLogger`, `UniqueWarningLogger`.
- [visualization/](src/main/java/hu/bme/mit/theta/common/visualization/) — `Graph`/`Node`/`Edge` + attributes; `writer/` renders; `WebDebuggerLogger` feeds the ARG web debugger.
- [dsl/](src/main/java/hu/bme/mit/theta/common/dsl/) — `Scope`/`Symbol`/`Env`/`SymbolTable` symbol-resolution contract (see invariant 4).
- [parser/](src/main/java/hu/bme/mit/theta/common/parser/) — Lisp S-expression lexer/parser (`LispParser`, `SExpr`); used by core's legacy `parser/` stack.
- [collection/](src/main/java/hu/bme/mit/theta/common/collection/) — `CollectionUtil` + pluggable factories (see invariant 1).
- [datalog/](src/main/java/hu/bme/mit/theta/common/datalog/) — small Datalog engine; currently no consumers outside its own package/tests.
- [table/](src/main/java/hu/bme/mit/theta/common/table/) — CSV/HTML table writers (benchmark output); [stopwatch/](src/main/java/hu/bme/mit/theta/common/stopwatch/) — timing; [process/](src/main/java/hu/bme/mit/theta/common/process/) — `SimpleProcessRunner` (external process wrapper, Kotlin); [exception/](src/main/java/hu/bme/mit/theta/common/exception/) — `NotSolvableException` (thrown by e.g. `CexMonitor` on refinement stall).
