# SV-COMP 2027 frontend and soundness work (`svcomp27-fixes` → `master`)

**Status: draft, not yet opened.** Numbers below are measured unless explicitly marked otherwise.

## What this is

A long-running effort to make theta's C frontend get through the SV-COMP benchmark suite, and to
make the answers it produces trustworthy. 473 commits, 229 source files, concentrated in the
frontend and the XCFA construction:

| area | +/- |
|---|---|
| `frontends/c-frontend` | 9562 / 572 |
| `xcfa/c2xcfa` | 6895 / 212 |
| `xcfa/xcfa` (passes) | 6358 / 468 |
| `xcfa/xcfa-cli` | 3362 / 657 |
| `xcfa/xcfa-analysis` | 982 / 327 |
| `common/core` | 712 / 83 |
| solver backends (smtlib, z3, z3-legacy, javasmt) | 918 / 191 |

73 feature-guard fixtures and 268 sampled SV-COMP tasks, in a canary suite that now runs as a
Gradle task (`./gradlew :theta-xcfa-cli:canaryTest`).

## Measured impact

Full portfolio, 36,531 runs. Runs 93/98/99 are 7 GB; **run 102 is the competition's real
allocation (15 min / 15 GB / 2 cores)** and is the number to quote:

| | run 93 (see below) | run 98 | run 99 | **run 102 (15 GB)** |
|---|---|---|---|---|
| **score** | 19,835 | 13,407 | 21,605 | **22,536** |
| correct | 12,890 | 13,905 | 14,349 | **14,866** |
| wrong | 55 | 528 | 71 | **72** |
| error | 23,173 | 21,684 | 21,697 | **21,176** |

**+2,701 over run 93 at the real allocation, +1,976 correct answers, with the wrong count up
by 17 (55 -> 72).** At an identical 7 GB budget the branch is +1,770 (run 99), so roughly a third of
the headline gain is the memory budget rather than this work -- though run 102 also used a different
host and CPU model, so memory and hardware are not separated.

Of the 24 results wrong in run 102 that were not wrong in run 93, **23 were ERRORs there** and
one was correct (limitation 1 below).

### Against the shipped release

`theta v7.3.1` (run 2026-07-16, published at share.mit.bme.hu) on the **same 36,531 tasks**, after
normalising task paths:

| | theta v7.3.1 (8 GB, STABLE) | **run 102 (15 GB, COMPLEX27)** |
|---|---|---|
| **score** | 8,071 | **22,536** |
| correct | 6,017 | **14,866** |
| **wrong** | 147 | **72** |
| **genuine tool errors** | **16,194** | **2,337** |
| timeout | 11,559 | 16,054 |
| out of memory | 2,577 | 2,785 |
| other / unknown | 40 | 417 |

**+14,465, with roughly half the wrong answers — and genuine tool errors down 86% (16,194 → 2,337).**

That split is the substantive result, and it is easy to miss if "error" is read as one bucket.
BenchExec's `error` category covers both "the tool failed" and "the tool ran out of time or memory".
Separating them: the release's failures are mostly **the frontend refusing the program** (16,194),
while this branch's are mostly **timeouts** (16,054) — tasks that now actually run and exhaust their
900 s instead of failing in seconds. Resource exhaustion rose (14,136 → 18,839) precisely *because*
far more tasks get far enough to consume resources.

Memory moves the split within that bucket rather than the total: 7 GB → 15 GB took OOM from 6,331 to
2,785 and timeouts from 13,159 to 16,054. 144 of the release's 147 wrong verdicts are no
longer wrong; 3 remain. Of the 69 that are wrong here and not there, **68 were ERRORs in the release**
— tasks that only now get far enough to answer — and exactly one was correct:
`pthread-divine/tls_basic` (unreach-call), which the release answers `true` and this branch answers
`false`. That is a second correct→wrong case beyond limitation 1 and is not yet diagnosed.

Caveats, all real: the release ran `--portfolio STABLE` (complex26) at 8 GB, this run COMPLEX27 at
15 GB. Memory is not the driver — run 99 at **7 GB**, below the release's 8 GB, still scores 21,605.
The portfolio difference is genuine and part of what this branch delivers, but it means the number is
not attributable to the frontend fixes alone. Note also that upstream `master` has moved on since
v7.3.1 (origin is at `9538c9ce76`), so this compares against a shipped release, not against current
upstream.

⚠️ **"Run 93" is not master.** It is a mid-branch state built 2026-08-16, six weeks and dozens of
commits after master's tip (`22ab2b88de`, 2026-07-06). It is the right reference for *this batch's*
delta, but it is NOT the master→branch delta, and nothing above should be read as one. There is no
full-portfolio measurement of master, because master fails the frontend outright on whole families
(termination, product-lines), so those tasks have no master verdict to compare against.

The only master data available is a **Concurrency-only** run at the merge-base
(`baseline-master-22ab2b88de-oc-userprop/`): one config, OC + Z3 propagator, 4 properties, 3,176
tasks — all of which run 102 also covers:

| on those 3,176 tasks | master `22ab2b88de` | run 102 |
|---|---|---|
| score | 2,405 | **3,262** |
| correct | 1,418 | **1,967** |
| error | 1,751 | **1,197** |
| wrong | 5 | 10 |

**+857 on the shared subset.** Read it with care: master ran a *single* OC config while run 102 ran
the whole COMPLEX27 portfolio, so part of that gap is the portfolio having more configs to try, not
this branch's fixes. It is indicative, not a controlled comparison.

### Two families that the release could not read at all

Three targeted runs after the full portfolio, each answering one question. They move no score --
both families are still at zero correct -- but they are the clearest evidence of what the frontend
work did and did not buy.

**intel-tdx-module** (836 runs, `unreach-call`, 15 min / 15 GB):

| | v7.3.1 | run 102 | run 105 | **run 108** |
|---|---:|---:|---:|---:|
| frontend error | 836 | 166 | 112 | **0** |
| out of memory | 0 | 313 | 290 | 442 |
| timeout | 0 | 357 | 434 | 394 |
| solved / wrong | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |

**Every intel-tdx task now builds.** Run 105 also exposed a regression introduced by this branch --
a `CPointer cannot be cast to CStruct` on a lvalue branch that asserted a type instead of resolving
it, which took 20 tasks backwards from out-of-memory to frontend error. It is fixed (`37e3a3cf94`),
and run 108 confirms the predicted outcome stated in that commit *before* the run: the remaining 112
errors became out-of-memory, score unchanged at 0.

What blocks the family now is capacity with a named cause: it falls `multi` -> `flat` -> `bytes` on
one construct (`Taking the address of a multi-byte member of a byte-addressed union is not
supported`), and 210 KB of firmware at one cell per byte does not fit in 15 GB.

**libvsync** (87 runs at 60 min / 30 GB -- 4x the time and 2x the memory of a competition slot,
across CEGAR/EXPL, CEGAR/PRED_CART and MDD): 45 timeouts, 25 runs raising theta's own
`IllegalStateException: Cannot handle dereferences with changed variables in between` inside an
`ATOMIC_BEGIN` block, 8 MDD/solvability errors, 7 lost to a solver misconfiguration on the
reviewer's side of the fence (Z3-legacy cannot interpolate bitvectors), **0 correct** and **2
wrong** -- both the same `bounded_mpmc_check_full` false alarm. An earlier run at the same budget
with OC alone (29 runs) also solved nothing.

That false alarm is now reproduced by three independent configurations (EXPL, PRED_CART, and the
COMPLEX27 portfolio in run 102), which locates it in the **race detection itself** rather than in a
domain, solver or POR setting. It is the single best-localised soundness target in the branch.

Run 98 is in the table deliberately: it is the same work *before* the last two fixes, and it scored
6,428 **below** run 93. That dip was 456 Juliet
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
own storage width; a bitfield reached through a narrowing; a struct copied through a pointer; brace elision over an
array of unions; an aggregate assigned by copying its storage; and a copied aggregate's type
resolved rather than asserted.

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

- **Canary suite**: 268 real SV-COMP tasks + 73 feature-guard fixtures, green on every commit that
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

0. **Two tasks go correct → wrong against the shipped release**: `ldv-regression/rule60_list2`
   (item 1 below, diagnosed) and `pthread-divine/tls_basic` (unreach-call, **not yet diagnosed** —
   found only when comparing against v7.3.1). Both deserve a look before merge.
1. **`ldv-regression/rule60_list2` regressed from correct to wrong.** Bisected to `c8cf3c3ba9`, but
   the wrong answer is **not** that commit's: on every build, including pre-branch ones,
   `--arithmetic bitvector` answers `Unsafe` on this safe program while `integer` answers `Safe`.
   That commit only changed which encoding the task is routed to. A pre-existing bitvector defect,
   newly exposed. It is the only case in the whole branch where a working answer was taken away.
2. **23 further results are wrong in run 102 that were not wrong in run 93 — all 23 were
   ERRORs there.** Latent unsoundness exposed by tasks that now get far enough to answer, not caused.
   11 are wrong-`true` (−32 each), which is the expensive direction and worth triaging first. The
   wrong count rose 55 → 72 across the branch; that is the honest cost of answering 1,976 more tasks.
3. **intel-tdx and libvsync parse completely and answer nothing.** 836 + 52 tasks moved from "cannot
   be read" to "cannot be finished", which is worth zero points. tdx is capacity-bound behind the
   byte-addressed fallback described above; libvsync does not converge under OC, CEGAR (either
   domain) or MDD even at 60 min / 30 GB. Neither is a merge blocker -- both were unusable before --
   but neither should be presented as solved.
4. **A regression this branch introduced was caught by benchmark, not by tests.** The
   `CPointer cannot be cast to CStruct` cast (limitation above) shipped in `ce78ed430b`, survived the
   canary suite and the unit tests, and was only visible as 112 identical failures in an 836-run
   family benchmark. It is fixed, but no fixture guards it: the shape that triggers it has not been
   reduced to one, and the tdx sources are too large to run as canary rows. **The guard is the run.**
5. **The stub-range fix works but is unexplained.** It turned 456 Juliet tasks from wrong to correct
   (456/456, with 456 `_bad` controls still caught), yet five minimal programs of the obvious shape
   verify the same with and without it. Guarded by 6 canary rows rather than a fixture, because a
   fixture that does not discriminate guards nothing.
6. **8 ntdrivers tasks still refuse** `Toc->TrackData[0] = Toc->TrackData[i]`. The cause is known —
   the right-hand element address loses its struct `cType` and the frontend derives `CUnsignedInt`
   from the sort — and the obvious fix was tried and reverted for regressing pointer assignments.
7. **`CComplexType.getType` is not stable across calls** for the same expression. Found incidentally;
   unchased; likely explains other identity-keyed metadata surprises.
8. **The byte-addressed model refuses floats.** Deliberate: SMT-LIB's FP sort has a single NaN, so
   `fp.to_ieee_bv` cannot preserve a payload, and MathSAT does not implement it at all. Loud refusal
   over a quiet wrong answer.
9. **Pre-existing formatting violations** in ~12 files. This branch adds none — verified by comparing
   the violation list against `master` — but does not fix them either.

## Review guidance

The frontend diff is large but most of it is comments explaining *why*, and tests. The places where
judgement is embedded, and where review is most valuable:

- `LibraryStubsPass` — what a stub havocs and how it is bounded. Item 5 above is unexplained.
- `MemoryFunctionsPass.nondetFillLoop` — the loop lowering, and the deliberate refusal that remains:
  a pointer to a compound under the typed-cell models, where a per-byte havoc would be invisible to a
  sibling read at a wider type.
- `ByteMemoryPass` — the decision to refuse floats rather than encode them.
- `FrontendXcfaBuilder.copiedStructOrNull` / `structuralBitfieldWrites` — the two lvalue families.
- `ExecuteConfig.frontend` — the fallback chain (`multi` → `flat`, and → `bytes`), and which failures
  are recoverable.
- `BitwiseChecker` — it now decides the arithmetic encoding for more programs, which is how
  limitation 1 surfaced.

`benchmark-results/PLAN.md` is the long-form record: every batch, every root cause, every measurement
including the ones that came out negative.
