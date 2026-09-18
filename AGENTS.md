# Theta — how to use

## Build
- `./gradlew build` — full build
- `./gradlew :theta-<x>-cli:build` — build one CLI tool
- `./gradlew :theta-<x>-cli:shadowJar` — fat jar for that tool

Gradle module names are `theta-<dirname>` (`settings.gradle.kts` prefixes them) — `:xcfa-cli:build` does **not** resolve, use `:theta-xcfa-cli:build`.

Each CLI targets its own formalism / use case; see the module's own `README.md` for how to run it and its input formats:
- `xcfa-cli` — C / software programs (sequential and concurrent), Btor2 circuits
- `xsts-cli` — XSTS: statecharts (Gamma backend), Petri nets (PNML, experimental)
- `cfa-cli` — CFA (e.g. as a PLCverif verification backend)
- `sts-cli` — STS: AIGER (hardware model checking)
- `xta-cli` — Uppaal timed automata
- `ltl-cli` — LTL properties
- `solver-smtlib-cli` — install/manage SMT-LIB solvers

## Run
- `./gradlew :theta-<x>-cli:run --args="..."`, or
- `java -cp ... hu.bme.mit.theta.<x>.cli.<X>Cli ...` (main class per tool, e.g. `hu.bme.mit.theta.xcfa.cli.XcfaCli`)

Required env: `LD_LIBRARY_PATH=$PROJECT_DIR/lib/` (for native solvers). Some setups use JDK 21 (`/usr/lib/jvm/java-21-openjdk`).

If your local `.idea/workspace.xml` has IntelliJ run configurations (it's gitignored and per-developer — not in a fresh clone), they're a useful source of example invocations: read a config's main class + program args + JVM args and replicate on the command line.

## Local verification loop

⚠️ **`timeout N theta-start.sh …` does NOT kill the verifier.** The script does not `exec` — it launches a child JVM — so the timeout kills the *script* and leaves the JVM orphaned, still holding the pipe. Any caller reading that pipe (a `$(...)` capture, a `while read` loop) then hangs **forever**, long after the timeout should have fired, and the run looks stuck rather than timed out. Kill the JVM itself (`pkill -f 'theta.jar.*<input path>'`) to release it. This is why a batched local suite appears to wedge on one task — it is not the task being slow.

- Fat jar for fast iteration: `./gradlew :theta-xcfa-cli:shadowJar` → `subprojects/xcfa/xcfa-cli/build/libs/theta-xcfa-cli-<version>-all.jar`.
- Running the jar directly needs `LD_LIBRARY_PATH=<dist>/lib` (legacy Z3) and `--smt-home <dist>/solvers`. The packaged `theta-start.sh` (template at `scripts/theta-start.sh`) sets these but hardcodes `-Xmx14210m -Xss120m`.
- Full distribution: `./gradlew buildArchiveTheta-svcomp -x test` → `subprojects/xcfa/xcfa-cli/build/distributions/Theta-svcomp.zip`. After any rebuild also `rm -rf subprojects/xcfa/xcfa-cli/build/distributions/Theta-svcomp` — a stale extracted directory is silently reused.
- Parse-only smoke test: `--svcomp --backend NONE --loglevel RESULT --property <prp> --architecture ILP32|LP64` (success marker: `ParsingResult Success`).
- Canary regression gate: `./gradlew :theta-xcfa-cli:canaryTest` builds the `Theta-svcomp` distribution and runs ~268 real sv-benchmarks tasks (parse-only by default — `--backend NONE` per task; `-Ptheta.canary.mode=full` checks verdicts instead) plus the feature-guard fixtures. The fixtures alone — the fast half, a few minutes — are `:theta-xcfa-cli:fixtureTest`. **Run this before any frontend or pass change lands.** For each new frontend/grammar capability add a `canaries/fixtures/` program that fails before your change and passes after, and a `fixtures/fixtures.tsv` row. See `subprojects/xcfa/xcfa-cli/canaries/README.md`.

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

Two doc systems exist. **Prefer per-subproject `README.md` / `AGENTS.md` for edit-time detail** — the files below are broader/older background.

### `doc/` — project-level guides (flat markdown)
- `Build.md` — JDK 21 + Gradle setup, platform notes.
- `Development.md` — dev environment, tooling, workflow entry point.
- `Coding-conventions.md` — Java style rules (DO / AVOID / DO NOT), formatting, copyright headers.
- `CI.md` — CI/CD, collaboration standards, release process.
- `CEGAR-algorithms.md` — CEGAR configuration options + best practices. Read before touching `common/analysis`.
- `Portfolio.md` — portfolio mechanism: automatic algorithm/config selection.
- `LBE.md` — Large Block Encoding design note (+ `LBE-images/`), Dec 2021.
- `Tools.md` — the competition tool variants (Theta / EmergenTheta / Thorn / ThetaCHC).
- `copyright-header.txt` — header prepended to every source file.

### `doc/wiki/` — MkDocs-Material site (published wiki)
Built by the `buildDocs` Gradle task (`buildSrc/docs-builder.gradle.kts`) and **deployed by CI on every release** to the `gh-pages` branch under `wiki/` (the same branch hosts `javadoc/` and the publications page).

The wiki **mirrors markdown that lives elsewhere in the repo** — it holds almost no content of its own. `doc/wiki/hooks.py` discovers, and rewrites the relative links of:
- every `README.md` / `USING.md` / `AGENTS.md` under `subprojects/` (→ *Modules*; other filenames are ignored, as is anything under `build/` or `resources/`),
- every `*.md` under `doc/` (→ *Guides*), and the root `README.md` / `AGENTS.md`.

**Consequence: a file with one of those names is published the moment you add it — write accordingly.** Only `doc/wiki/docs/` (front page, contributing page) is wiki-owned.

### Publications
If a task has a trivial, direct need for a specific paper, the publication list is linked from `README.md`: <https://ftsrg.github.io/theta/publications/> (hosted from this repo's GitHub Pages branch). By default this is not needed — don't reach for it unless the task clearly calls for it.

## Formatting

Spotless (google-java-format AOSP + ktfmt) is required but not run automatically: `./gradlew spotlessApply` locally, or comment `\format` on the GitHub PR. Every source file needs the copyright header (`doc/copyright-header.txt`).

Spotless is configured `ratchetFrom("origin/master")` (`buildSrc/src/main/kotlin/java-common.gradle.kts`), so it only formats files that differ from `origin/master` — running `spotlessApply` is safe and does not reformat the whole repo. Do not defeat the ratchet to format everything.

`checkCopyright` derives the expected year from a file's **last commit date** (`git log -1`), so run `applyCopyright` *after* committing, never before — otherwise it writes the previous year and the check then fails.

## Committing

Only commit when explicitly asked. Commit messages: **short**, following the project's convention — and do **not** mention Claude/AI or add Claude co-author trailers.

## Commenting Conventions

A comment states what is not obvious from the code — a non-trivial decision or its justification. It is not a place for the history of a bug, a measurement, or a rationale essay.

- Do NOT write more than 2-3 (reasonably long) lines of comment at one place (non-javadoc comments)
- Do NOT write paragraphs longer than 5-6 lines 
- Do write at most 2 paragraphs per method (javadoc style)
- Do write at most 4 paragraphs per class (javadoc style)
- Do write comments only about non-trivial development decisions and justifications
- Do NOT write comments about basic functionality or irrelevant / temporary context
- Never reference benchmark runs, batches, or dates in a comment

## On-demand deep docs

Documented modules follow a two-file convention (stated once here — the module files don't repeat it):
- `AGENTS.md` — how to **edit/extend** that module (invariants, change recipes). **Before editing files in a module, read that module's `AGENTS.md` first if it has one**, then keep it open while you work. Some agents auto-load it, others do not, so read it explicitly rather than relying on that. A few modules carry a deeper `AGENTS.md` for one package (e.g. `common/core/.../type/`, `common/analysis/.../algorithm/`) — read it too when you touch that package. Conceptual overviews stay in the module's `README.md`.
- `USING.md` — how to **consume** that module's API from elsewhere (cookbook). Read it explicitly when the task matches, via the pointers below.

Current pointers:
- Building/manipulating core exprs, stmts, valuations, or talking to solvers from **any** module: `subprojects/common/core/USING.md`.
- Binding a formalism to a checking algorithm (CEGAR, BMC/k-ind/IMC, IC3, MDD, CHC, LTL): `subprojects/common/analysis/USING.md`.
- Shared utilities (logging, DispatchTable, tuples, visualization, DSL scopes, deterministic collections): `subprojects/common/common/USING.md`.
- Getting/driving SMT solvers (factories, managers, unsat cores, interpolation, Horn, pooling, backend choice): `subprojects/solver/solver/USING.md`.
- Round-tripping core exprs/stmts through text (parse `toString()` back) or JSON-serializing ARG/Trace: `subprojects/common/grammar/USING.md`.

## Running one module's tests

`./gradlew :theta-<module>:test` (e.g. `:theta-xcfa-analysis:test`). Full suite: `./gradlew test`. Native solvers need `LD_LIBRARY_PATH=$PROJECT_DIR/lib/` (see Run).

## Doc creation and upkeep

**No local AGENTS.md yet?** If you edit files under `subprojects/<family>/<module>/` and that module has no `AGENTS.md`, before finishing the task ask the developer:

> *"This is my first time editing `<module>` — want me to draft a `AGENTS.md` here capturing build target, tests, invariants, and integration points I learned? (y/N)"*

Only draft on yes. Never do it silently. This project has multiple contributors — don't assume; ask.

**Module already documented?** Then upkeep is part of your edit, not a separate favor:
- If your change makes a statement in the module's `AGENTS.md`/`USING.md` wrong (renamed class, changed signature/invariant, extra step in a recipe), update that doc **in the same change** — no need to ask. State what you updated in your summary.
- If you *learned* something the docs lack (a non-obvious invariant, a gotcha that cost you time), propose a one-liner addition at the end of the task — ask, don't add silently.
- Never add suspected bugs/smells to these docs — those go to `possible-issues.md` at the repo root (and when you fix one, delete its entry there).
- Same applies to the root file you're reading: if the subproject map or a pointer here went stale, fix it.