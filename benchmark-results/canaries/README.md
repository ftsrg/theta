# Canary regression suite

Fast checks run after a Theta-svcomp build to catch frontend/analysis regressions before a
full benchmark. Point them at an extracted `Theta-svcomp` dir (or let them auto-extract the
sibling `Theta-svcomp.zip`). Java 21+ must be on `PATH` (the launcher uses `theta-start.sh`).

## `run_canaries.sh [THETA_DIR] [parse|full] [TSV]`

- **parse** (default): frontend-only smoke test (`--backend NONE`) over `canaries.tsv` — 255
  real sv-benchmarks tasks, one PASS per `ParsingResult Success`. The frontend *builds the
  XCFA* under `--backend NONE`, so this catches c2xcfa regressions, not just ANTLR ones. In
  this mode it also runs the feature-guard fixtures (below) and folds their result into the
  exit status.
- **full**: real `--portfolio STABLE` run comparing the printed verdict against
  `expected_verdict`. Slow — use a small `TSV` subset (e.g. `guard_set.tsv`).

`canaries.tsv` is a broad ~3-per-subfolder sample: good at detecting *general* breakage, but a
given task only *happens* to exercise a feature. That is what the fixtures are for.

## `run_fixtures.sh [THETA_DIR]` — feature guards

Each file under `fixtures/` is a minimal program that isolates one frontend/grammar
modification, so it builds **iff** that modification is present; reverting the fix flips its
outcome and the suite goes red. `fixtures/fixtures.tsv` maps each fixture to its arithmetic,
architecture, expected outcome (`PARSE-OK` / `FRONTEND-FAIL`), and the batch it guards. Run
directly, or automatically as part of `run_canaries.sh ... parse`.

Add a fixture when a batch adds a frontend/grammar capability: write the smallest program that
needs it, confirm it builds now, and add a row. Verdict-level bugs (a fix changes the *answer*,
not whether it builds) belong in `guard_set.tsv`, not here — e.g. the deferred packed-bitfield
memsafety wrongs (`test-bitfields-*`) are tracked there as known-wrong until slicing lands.

## `atomic_qual.tsv` — `_Atomic`-qualifier verdict guard

The 44 tasks of `sv-benchmarks/c/pthread-atomic-qualifier/` (the atomic-qualifier MR), keyed on
their real property/verdict. Run in **full** mode — `run_canaries.sh "" full atomic_qual.tsv` — to
check that `_Atomic` on a struct field, array element, whole struct, nested field or pointee still
makes concurrent accesses race-free (and that plain cells still race). 40 are green; 4 are the
known-open cases documented in `PLAN.md` (batch 62): `cast-ptr`/`funcptr` don't parse, and the two
`param-*` cast-through-a-cast tasks report a false race. Fast (~2.5 s each). The in-repo counterpart
that runs without an sv-benchmarks checkout is `XcfaDataRaceTest.testAtomicCellDataRace`.
