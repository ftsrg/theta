# SV-COMP 2027 frontend and soundness work (`svcomp27-fixes` → `master`)

**Status: draft, not yet opened.** Numbers below are measured unless explicitly marked otherwise.

## What this is

A long-running effort to make theta's C frontend get through the SV-COMP benchmark suite, and to
make the answers it produces trustworthy. 459 commits, 258 source files, ~28.9k added / 2.6k removed,
concentrated in the frontend and the XCFA construction:

| area | +/- |
|---|---|
| `frontends/c-frontend` | 9562 / 572 |
| `xcfa/c2xcfa` | 6895 / 212 |
| `xcfa/xcfa` (passes) | 6358 / 468 |
| `xcfa/xcfa-cli` | 3362 / 657 |
| `xcfa/xcfa-analysis` | 982 / 327 |
| `common/core` | 712 / 83 |
| solver backends (smtlib, z3, z3-legacy, javasmt) | 918 / 191 |

73 new test files, and a canary suite that now runs as a Gradle task.

## Measured impact

Full portfolio, 36,531 runs. Runs 93/98/99 are 7 GB; **run 102 is the competition's real
allocation (15 min / 15 GB / 2 cores)** and is the number to quote:

| | run 93 (baseline) | run 98 | run 99 | **run 102 (15 GB)** |
|---|---|---|---|---|
| **score** | 19,835 | 13,407 | 21,605 | **22,536** |
| correct | 12,890 | 13,905 | 14,349 | **14,866** |
| wrong | 55 | 528 | 71 | **72** |
| error | 23,173 | 21,684 | 21,697 | **21,176** |

**+2,701 over the baseline at the real allocation, +1,976 correct answers, with the wrong count up
by 17 (55 -> 72).** At an identical 7 GB budget the branch is +1,770 (run 99), so roughly a third of
the headline gain is the memory budget rather than this work -- though run 102 also used a different
host and CPU model, so memory and hardware are not separated.

Of the 24 results wrong in run 102 that were not wrong in the baseline, **23 were ERRORs there** and
one was correct (limitation 1 below).

Run 98 is in the table deliberately: it is the same work *before* the last two fixes, and it scored
6,428 **below** baseline. That dip was 456 Juliet
tasks answering `false(no-overflow)` on correct programs, and it is the clearest evidence in this PR
that error-count improvements mean nothing on their own — see "How this was validated".

Parse-only, 72,103 runs: frontend errors fell 580 (2,982 → 2,850 before-parsing, 1,518 → 1,070
after-parsing), netting +330 tasks that build. ~250 of that reduction returns as OOM/TIMEOUT, which
is consistent with tasks now getting further before failing.

Run 102 was raced on two clusters and the slower one stopped; the winner is the one reported. The
two hosts used different CPU models, so its wall-clock timings are not comparable with the others.

## What changed

**Frontend correctness.** Struct tags cached while their own body was still being read; declared-
but-undefined functions having no referencable id; assignment through width/sign wrappers; `extern`
arrays of unspecified extent (a *declaration*, not a sizing failure); compound bitwise assignments
selecting the wrong arithmetic encoding; union cells spliced at a placeholder type rather than their
own storage width; a bitfield reached through a narrowing; a struct copied through a pointer.

**Library modelling.** `calloc`, symbolic `memset`, `va_arg`, variadic arity, `pthread_detach`, and a
`LibraryStubsPass` for the stdio/string functions nothing defined — with the stub's havoc bounded to
the C type it writes, exactly as `__VERIFIER_nondet_<type>()` is bounded.

**Encodings.** Subnormal float decoding; INT_MIN negation widening in the bitvector overflow check;
`ExprSimplifier` folding through rebuilt operands; a byte-addressed memory model that now refuses
floats loudly rather than modelling them wrongly; and a fallback into that model for unions the
cell-per-value models cannot express.

**Diagnostics.** Several error messages now name the C type, the declaration, or the struct's fields.
This is not cosmetic: two separate bugs hiding behind one `Could not handle left-hand side` message
were only separable once the message printed C types, and "both sides are CStruct" was actively
misleading until it printed fields.

## How this was validated

- **Canary suite**: 268 real SV-COMP tasks + 69 feature-guard fixtures, green on every commit that
  ships. Now registered as `./gradlew :theta-xcfa-cli:canaryTest` (see below).
- **Per-module unit tests**, run one module at a time.
- **A/B for every fix**, rebuilding both sides. Several changes were implemented, measured at zero
  effect, and reverted rather than shipped.
- **Benchmarks**, with each new wrong result classified by what it scored in the baseline.

Three things were deliberately **not** shipped after measurement: an automatic bytes-model fallback
that would have converted ~554 score-0 errors into wrong verdicts; a `cType`-metadata fix measured at
zero effect; and a widened struct-copy guard that regressed working tasks. Each is recorded in
`PLAN.md` with the evidence, so they are not re-attempted blindly.

## Known limitations — please read before merging

1. **`ldv-regression/rule60_list2` regressed from correct to wrong.** Bisected to `c8cf3c3ba9`, but
   the wrong answer is **not** that commit's: on every build, including pre-branch ones,
   `--arithmetic bitvector` answers `Unsafe` on this safe program while `integer` answers `Safe`.
   That commit only changed which encoding the task is routed to. A pre-existing bitvector defect,
   newly exposed. It is the only case in the whole branch where a working answer was taken away.
2. **23 further results are wrong in run 102 that were not wrong in the baseline — all 23 were
   ERRORs there.** Latent unsoundness exposed by tasks that now get far enough to answer, not caused.
   11 are wrong-`true` (−32 each), which is the expensive direction and worth triaging first. The
   wrong count rose 55 → 72 across the branch; that is the honest cost of answering 1,976 more tasks.
3. **The stub-range fix works but is unexplained.** It turned 456 Juliet tasks from wrong to correct
   (456/456, with 456 `_bad` controls still caught), yet five minimal programs of the obvious shape
   verify the same with and without it. Guarded by 6 canary rows rather than a fixture, because a
   fixture that does not discriminate guards nothing.
4. **8 ntdrivers tasks still refuse** `Toc->TrackData[0] = Toc->TrackData[i]`. The cause is known —
   the right-hand element address loses its struct `cType` and the frontend derives `CUnsignedInt`
   from the sort — and the obvious fix was tried and reverted for regressing pointer assignments.
5. **`CComplexType.getType` is not stable across calls** for the same expression. Found incidentally;
   unchased; likely explains other identity-keyed metadata surprises.
6. **The byte-addressed model refuses floats.** Deliberate: SMT-LIB's FP sort has a single NaN, so
   `fp.to_ieee_bv` cannot preserve a payload, and MathSAT does not implement it at all. Loud refusal
   over a quiet wrong answer.
7. **Pre-existing formatting violations** in ~12 files. This branch adds none — verified by comparing
   the violation list against `master` — but does not fix them either.

## Review guidance

The frontend diff is large but most of it is comments explaining *why*, and tests. The places where
judgement is embedded, and where review is most valuable:

- `LibraryStubsPass` — what a stub havocs and how it is bounded. Item 3 above is unexplained.
- `ByteMemoryPass` — the decision to refuse floats rather than encode them.
- `FrontendXcfaBuilder.copiedStructOrNull` / `structuralBitfieldWrites` — the two lvalue families.
- `ExecuteConfig.frontend` — the fallback chain (`multi` → `flat`, and → `bytes`), and which failures
  are recoverable.
- `BitwiseChecker` — it now decides the arithmetic encoding for more programs, which is how
  limitation 1 surfaced.

`benchmark-results/PLAN.md` is the long-form record: every batch, every root cause, every measurement
including the ones that came out negative.
