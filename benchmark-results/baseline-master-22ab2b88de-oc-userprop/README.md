# Master OC baseline — `22ab2b88de`, Z3 user propagator

**This is the reference baseline. Every follow-up OC benchmark is compared against it.**

- Commit: `22ab2b88de` ("version bump") on `master` — i.e. Theta *without* any of the
  svcomp27-fixes branch work.
- Benchmark: `xmls/theta27-conc-userprop.xml`, run on sosy 2026-07-28 09:37:54.
- Scope: full Concurrency set, **one** config (OC + `PROPAGATOR` decision procedure, Z3),
  4 properties — `unreach-call`, `no-data-race`, `valid-memsafety`, `no-overflow`.
- Limits: as in the xml (CPU-pinned per the standing rule).
- Source on sosy: `/data/scratch/bajczi/results/Theta-master-22ab2b88de/theta27-conc-userprop.xml/2026-07-28_09:37:54/`

Contents: the 4 `.xml.bz2` result files plus `*.logfiles.zip` (per-run tool output).

## Why master is only a *partial* baseline

Master is a valid baseline **for the OC/concurrency configs only**. It is *not* a valid baseline
for the full `theta27-short.xml` portfolio: on the termination and product-lines families
(`*_cilled_*`, `email_spec*`, `elevator_*`) master fails the frontend outright in 1.4–3.0 s, so
those tasks have no master verdict to regress from. For portfolio comparisons use
`results-2026-07-24_04-26-batch61` instead.

## Known regression class when comparing against this baseline

Tasks where master's OC stage **crashed fast** (`IllegalStateException` at
`XcfaToEventGraph.kt:232`, exit 202) and fell through to a config that solved them will look like
timeouts on newer builds: our OC fixes removed the crash, so OC now genuinely runs to its
`timeoutMs = 250_000` (exit 201) before falling through. That is the cost of the fix, not a new
defect — and it only overruns because the short benchmark uses a 300 s limit, whereas the
portfolio timeouts are tuned for SV-COMP's real 900 s budget.
