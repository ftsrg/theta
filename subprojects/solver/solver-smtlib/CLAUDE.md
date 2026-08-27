# solver/solver-smtlib — notes for editing this module

Gradle module: `:theta-solver-smtlib`. Drives **external SMT-LIB v2 solver processes** behind `:theta-solver`'s interfaces, and owns the solver-binary install/version framework rooted at `~/.theta` (exposed as a CLI by `:theta-solver-smtlib-cli`). Names resolve as `"<solver>:<version>"` via [SmtLibSolverManager](src/main/java/hu/bme/mit/theta/solver/smtlib/SmtLibSolverManager.java) (`"latest"` is a reserved version keyword). Consumers never get this module directly — they register the manager (`SmtLibSolverManager.create(homePath, logger)`) into the static `SolverManager` registry themselves.

## Layout

- [solver/](src/main/java/hu/bme/mit/theta/solver/smtlib/solver/) — the machinery: `SmtLibSolver` (Solver+UCSolver), abstract `SmtLibItpSolver` (vendor subclasses only — **generic has no interpolation**), `binary/` (process I/O: interactive `GenericSmtLibSolverBinary` on NuProcess vs one-shot `GenericSmtLibOneshotSolverBinary` writing a temp `.smt2`), `transformer/` (Theta→SMT-LIB text), `parser/` (ANTLR `SMTLIBv2.g4` for responses), `model/` (`SmtLibModel` symbol→term strings; `SmtLibValuation` lazily parses per-`Decl`), `installer/` (template-method `SmtLibSolverInstaller.Default`: writes `solver.txt`/`solver-args.txt` under `home/<solver>/<version>/`), `SmtLibEnumStrategy` (`SORTS` default — uninterpreted sort + distinct consts, chosen because datatypes break interpolation on most solvers; `DATATYPES` opt-in per solver).
- [impl/generic/](src/main/java/hu/bme/mit/theta/solver/smtlib/impl/generic/) — the reference implementation, works with any conformant binary (SAT + unsat cores; no itp).
- [impl/<solver>/](src/main/java/hu/bme/mit/theta/solver/smtlib/impl/) — per-vendor overrides: a factory declaring capabilities, an installer with a hand-maintained version→URL table, and (for itp-capable solvers) a custom `ItpSolver`/`ItpMarker` pair.

## Capability matrix (verified per impl/, 2026-07)

| Solver | SAT | UC | Interpolation | Horn | Notes |
|---|---|---|---|---|---|
| generic | ✓ | ✓ | — | — | any SMT-LIB binary |
| z3 | ✓ | ✓ | ✓ (version-split: `(interp)` ≤4.5.0, `get-interpolant` ≥4.8.8, **none between**) | — | |
| mathsat | ✓ | ✓ | ✓ tree (≥5.4.0, `:interpolation-group`) | — | custom `IntRem` encoding |
| smtinterpol | ✓ | ✓ | ✓ bulk tree | — | Java jar, own factory (not Generic-derived) |
| princess | ✓ | ✓ | ✓ bulk tree | — | forces `SORTS` enum strategy; stderr suppressed |
| cvc5 | ✓ | ✓ | ✓ pairwise push/pop | — | enum strategy fixed `DATATYPES` |
| cvc4 | ✓ | ✓ | — | — | @Deprecated; `fp`-token parse workaround |
| bitwuzla / boolector | ✓ | ✓ / — | — | — | @Deprecated; installers compile from source |
| golem / eldarica | — | — | — | ✓ | one-shot binaries, `HORN` logic, `needsModelWrapping` for old versions |

## Invariants / gotchas

1. **Declarations mirror push/pop**: `SmtLibSolver` re-declares only consts not in its `declarationStack` — any change to add/track/push/pop must keep that stack exactly synchronized with solver scopes, or symbols vanish/duplicate after `pop`.
2. **Response parsing is ANTLR on full solver output** — vendor quirks are handled by flags on the binary layer (`Solver.CVC4` token stitching, `Solver.PRINCESS` stderr suppression), not by grammar forks. New quirk → new flag there, not a grammar copy.
3. **Interpolation is a per-vendor protocol**, subclassing `SmtLibItpSolver`; capability is *version-gated* (see matrix) and declared by the factory — a wrong gate silently produces `UnsupportedOperationException` at refinement time.
4. `getModel()`/`getUnsatCore()` are memoized and invalidated on any `add`/`pop`/`reset`; calling them off a SAT/UNSAT state throws.
5. Enum types: the chosen `SmtLibEnumStrategy` changes what assertions look like on the wire (SORTS wraps every enum-mentioning assertion) — interpolants/models must be interpreted under the same strategy.

## Adding a new external solver (checklist, from the existing impls)

1. `impl/<name>/<Name>SmtLibSolverFactory` extending `GenericSmtLibSolverFactory` — override the `create*` methods to declare capabilities (throw for unsupported).
2. `<Name>SmtLibSolverInstaller extends SmtLibSolverInstaller.Default` — version list, per-OS/arch archive URLs, default args.
3. Register the installer in `SmtLibSolverManager`'s constructor registry.
4. Interpolation: subclass `SmtLibItpSolver` + a marker class, following the closest protocol (pairwise: cvc5/z3-new; bulk tree: princess/smtinterpol; groups: mathsat).
5. Tests + a `solver-smtlib-cli` install smoke-run.
