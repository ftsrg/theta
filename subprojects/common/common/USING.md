# Using theta-common — utility cookbook

Consumer-facing counterpart of [CLAUDE.md](CLAUDE.md). Everything in Theta already depends on this module (`implementation(project(":theta-common"))`), so these are available everywhere.

## Logging

```java
Logger logger = new ConsoleLogger(Logger.Level.SUBSTEP);  // filters: level ≤ SUBSTEP printed
logger.write(Level.MAINSTEP, "Iteration %d%n", i);        // printf-style
logger.mainStep("Iteration %d", i);                       // helper = writeln(MAINSTEP, ...)
Logger none = NullLogger.getInstance();                   // the default in most create(...) APIs
```

Levels, coarse→fine: `RESULT`, `BENCHMARK`, `MAINSTEP`, `SUBSTEP`, `INFO`, `DETAIL`, `VERBOSE`. `UniqueWarningLogger` deduplicates repeated warnings; `FileLogger` writes to a file.

## Runtime type dispatch — `DispatchTable`

The house pattern for "switch on expression class" (this is how `ExprSimplifier` structures its 101 cases):

```java
DispatchTable<String> table = DispatchTable.<String>builder()
        .addCase(IntAddExpr.class, e -> "sum")
        .addCase(BoolLitExpr.class, e -> "lit")
        .addDefault(o -> "other")
        .build();
String r = table.dispatch(expr);
// DispatchTable2<P, R>: same, but handlers take an extra parameter (dispatch(obj, param))
```

## Small values & helpers

- `Tuple2.of(a, b)`, ... up to `Tuple7`, generic `TupleN` — structural equality; used pervasively as map keys.
- `Either<L, R>`, `Try<T>` (`Try.attempt(supplier)`), `Unit` — lightweight functional values.
- `Utils.lispStringBuilder("label").add(x).body().add(y)` — the `(label x y)` toString convention every core class follows.
- `Utils.singleElementOf(coll)`, `head`/`tail`, `anyMatch`/`allMatch`.
- `CollectionUtil.createMap()/createSet()` — **insertion-ordered** map/set (determinism; prefer these over bare `HashMap` in analysis code so runs stay reproducible).

## Visualization

Build a [Graph](src/main/java/hu/bme/mit/theta/common/visualization/Graph.java) (`Node`/`Edge` with `NodeAttributes`/`EdgeAttributes`), then render:

```java
String dot = GraphvizWriter.getInstance().writeString(graph);   // also: JSONWriter, YedWriter
```

Analysis-side helpers that produce `Graph`s (ARG/trace/MDD) live in `theta-analysis`'s `utils/` — see [analysis USING.md](../analysis/USING.md).

## Building a DSL frontend — `dsl/`

`Scope` (symbol lookup, nestable via `BasicScope(parent)`), `Symbol` (named entity), `SymbolTable`, `Env` (runtime bindings). This is the symbol-resolution contract used by core's DSL, `common/grammar`'s ANTLR base, and the solver SMT-LIB frontends — copy `common/core`'s `dsl/` usage as reference. The `parser/` package is a separate minimal Lisp reader (`LispParser`/`SExpr`) — only core's legacy parser uses it.

## Odds and ends

- `TableWriter` (`BasicTableWriter` CSV-style, `HtmlTableWriter`) — benchmark/result tables.
- `SimpleProcessRunner` (Kotlin) — run an external process with a timeout (`run(cmd, timeoutSeconds)`); sole consumer today is `common/ltl`'s external LTL→HOA converter.
- `NotSolvableException` — thrown to abort a verification run judged hopeless (e.g. `CexMonitor` divergence detection); catch it if you drive checkers in a portfolio.
- `IntMatrix`, `GrowingIntArray` — primitive-int structures backing zone DBMs.
- `OsHelper` — platform detection (native solver loading).
