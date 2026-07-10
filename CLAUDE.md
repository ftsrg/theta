# Theta — how to use

## Build
- `./gradlew :theta-xcfa-cli:build` — build xcfa-cli
- `./gradlew :theta-xcfa-cli:shadowJar` — fat jar
- `./gradlew build` — full build

Gradle module names are `theta-<dirname>` (`settings.gradle.kts` prefixes them) — `:xcfa-cli:build` does **not** resolve, use `:theta-xcfa-cli:build`.

## Run
IntelliJ run configs live in `.idea/workspace.xml` (e.g. `cir-example (1)`, `bmc-tracegen-example`, `btor2-horn`). Claude can't trigger them directly — replicate via:
- `./gradlew :xcfa-cli:run --args="..."`, or
- `java -cp ... hu.bme.mit.theta.xcfa.cli.XcfaCli ...`

Required env: `LD_LIBRARY_PATH=$PROJECT_DIR/lib/` (for native solvers). Some configs use JDK 21 (`/usr/lib/jvm/java-21-openjdk`).

To mirror a specific config: read its entry in `.idea/workspace.xml` for main class + program args + JVM args.

## Subproject map

Theta is organized as `subprojects/<family>/<module>`. The Gradle project name is `:theta-<module>` (e.g. `:theta-xcfa-cli` — the family is not part of the name).

Each formalism family tends to follow a `<name>` (model) + `<name>-analysis` (algorithms binding the model to CEGAR) + `<name>-cli` (executable tool) split.

- `common/` — shared foundations. `core` (Expr/Stmt/Type, Decl, Valuation), `analysis` (CEGAR, ARG, abstractors/refiners), `grammar` (ANTLR base), `ltl` + `ltl-cli`, `multi-tests`. Touch when adding a primitive or algorithm shared across formalisms.
- `solver/` — SMT backends: `solver-z3`, `solver-z3-legacy`, `solver-javasmt`, `solver-smtlib` (+ `-cli`), `solver-eldarica`, `graph-solver`. Touch when adding/fixing a solver or solver integration.
- `frontends/` — input parsers: `c-frontend` (via `llvm`), `btor2-frontend`, `chc-frontend`, `dve-frontend`, `promela-frontend`, and the Petri net stack (`petrinet-model`/`-analysis`/`-frontend`/`-xsts`). Touch when adding/fixing an input language.
- `xcfa/` — eXtended CFA: a forest of CFAs (procedures/threads) that can communicate. This is the primary path for **all** software verification now. Includes translators (`c2xcfa`, `btor2xcfa`, `litmus2xcfa`, `llvm2xcfa`, `xcfa2chc`) and `cat` (memory-model DSL). `xcfa-cli` is the main user-facing tool.
- `cfa/` — sequential control-flow automata. Stable and still used, but rarely developed further (most new software-verification work happens in `xcfa`).
- `xsts/` — eXtended symbolic transition systems. Commonly used for statecharts.
- `sts/` — symbolic transition systems. The AIGER frontend is STS-based; like `cfa`, older and stable — occasionally extended, but not a focus.
- `xta/` — timed automata.

## Documentation map

Two doc systems exist. **Prefer per-subproject `README.md` / `CLAUDE.md` for edit-time detail** — the files below are broader/older background.

### `doc/` — project-level guides (flat markdown)
- `Build.md` — JDK 21 + Gradle setup, platform notes.
- `Development.md` — dev environment, tooling, workflow entry point.
- `Coding-conventions.md` — Java style rules (DO / AVOID / DO NOT), formatting, copyright headers.
- `CI.md` — CI/CD, collaboration standards, release process.
- `CEGAR-algorithms.md` — CEGAR configuration options + best practices. Read before touching `common/analysis`.
- `Portfolio.md` — portfolio mechanism: automatic algorithm/config selection.
- `LBE.md` — Large Block Encoding design note (+ `LBE-images/`), Dec 2021.
- `copyright-header.txt` — header prepended to every source file.

### `doc/wiki/` — MkDocs-Material site, live but nearly content-empty
Sources under `doc/wiki/docs/`; built by the `buildDocs` Gradle task (`buildSrc/docs-builder.gradle.kts`) and **deployed by CI on every release** to the `gh-pages` branch under `wiki/` (the same branch hosts `javadoc/` and the publications page). Infrastructure dates to 2022; content was never written — the per-formalism and Frontends pages are "no content" stubs. Has real content only in: `index.md`, `Formalisms/index.md` (short intros), `Algorithms/index.md` (architecture overview, 2026-07). Don't cite stub pages as a source; conceptual truth lives in per-subproject READMEs.

### Publications
If a task has a trivial, direct need for a specific paper, the publication list is linked from `README.md`: <https://ftsrg.github.io/theta/publications/> (hosted from this repo's GitHub Pages branch). By default this is not needed — don't reach for it unless the task clearly calls for it.

## Formatting

Spotless (google-java-format AOSP + ktfmt) is required but not run automatically: `./gradlew spotlessApply` locally, or comment `\format` on the GitHub PR. Every source file needs the copyright header (`doc/copyright-header.txt`).

## On-demand deep docs

Documented modules follow a two-file convention:
- `CLAUDE.md` — how to **edit/extend** that module (invariants, change recipes). Auto-loads when you touch files there; never read it eagerly.
- `USING.md` — how to **consume** that module's API from elsewhere (cookbook). Never auto-loads — read it explicitly when the task matches, via the pointers below.

Current pointers:
- Building/manipulating core exprs, stmts, valuations, or talking to solvers from **any** module: `subprojects/common/core/USING.md`.
- Binding a formalism to a checking algorithm (CEGAR, BMC/k-ind/IMC, IC3, MDD, CHC, LTL): `subprojects/common/analysis/USING.md`.

## Running one module's tests

`./gradlew :theta-<module>:test` (e.g. `:theta-xcfa-analysis:test`). Full suite: `./gradlew test`. Native solvers need `LD_LIBRARY_PATH=$PROJECT_DIR/lib/` (see Run).

## When to propose a local CLAUDE.md

If you edit files under `subprojects/<family>/<module>/` and that module has no `CLAUDE.md`, before finishing the task ask the developer:

> *"This is my first time editing `<module>` — want me to draft a `CLAUDE.md` here capturing build target, tests, invariants, and integration points I learned? (y/N)"*

Only draft on yes. Never do it silently. This project has multiple contributors — don't assume; ask.