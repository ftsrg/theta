# Possible issues

Suspected bugs and smells found while working on something else. Delete an entry when it is fixed.

## `LDBL_*` macros do not match the modeled `long double`

`frontends/c-frontend/.../stdlib/MacroExprs.kt` gives the `LDBL_*` macros the IEEE double values
(`LDBL_MANT_DIG` 53, `LDBL_MAX` 1.797e+308, ...), while `ArchitectureConfig` models `long double`
as binary128 (113-bit significand, 15-bit exponent). x86 GCC uses the 80-bit extended format, which
matches neither. `LDBL_EPSILON` is also half the double epsilon (the old `DBL_EPSILON` mistake).

Today the floating-point ones carry a C `L` suffix that the value parser rejects, so a program
using them fails in the frontend instead of getting a wrong value. Dropping the suffix without
fixing the values (or the `long double` model) would turn that into a possible wrong verdict.

## Liveness-to-safety is unsound over unbounded integers

`L2SMEPass` reports termination when no state repeats. That implies termination only in a finite
state space, but under `--arithmetic integer` (and `efficient`, when it picks integers) signed C
variables are unbounded (`CastVisitor.signedCast` keeps them as they are). For `while (i > 0)
i = i + 1;` an inductive invariant like `__saved_ -> i > __saved_main::i` proves that no state
repeats, so BMC/KIND/IMC/IC3/MDD could answer that the program terminates. Termination validation
refuses this case (`LivenessWitness` needs finite types), verification does not.

## MDD confirms a wrong termination witness

With a `LivenessWitness`, MDD (`--backend MDD`, bitvector arithmetic) answered Safe for
`bounded-count-down.c` with a wrong state invariant after exploring 5 states, without reporting an
under-approximation. Plain bitvector MDD on the same program does not finish in 120 s. Termination
validation refuses MDD, MDD_CEGAR and IC3 for now (`ConfigToChecker.kt`).

## C statements never get their function name

`FunctionVisitor.propagateFunctionName` only sets a name when `getFunctionName()` is null, but
`CStatement.functionName` defaults to `""`, and it only descends into `CCompound`s. So
`CMetaData.functionName` is null for ordinary statements, and `YamlWitnessWriter`'s
violation-witness assumptions, which keep a local only if its function matches, drop every local
variable. `DssWitnessContent` infers the function from the locals a statement uses instead.

## MathSAT 5.6.15 crashes the JVM on some nonlinear integer tasks

SIGSEGV in `msat::QNumber::normalize` (`libmathsat5j.so`) on sv-benchmarks `divbin*`, `prod4br-ll*`
and `sqrt1-ll*` under DSS. Earlier runs on 5.6.11 (before the JavaSMT 6 bump) did not crash there,
but they used MathSAT for fewer queries. A native crash ends the run, so no fallback catches it.

## The Z3 term transformers throw `AssertionError("Unsupported sort: (_ FloatingPoint ...)")`

`Z3TermTransformer` (legacy and new) does on some float tasks; being an `Error`, it escapes every
`catch (e: Exception)` fallback, including DSS's checker and solver fallbacks.

## DSS rejects a procedure whose entry lies on a cycle

`while_infinite_loop_{1,2,3}`: the `BlockGraph` check `must have exactly one root block (no
predecessors), but found 0 among [SB1]` fails for `MIN_CUT_ABSORB_SELF_LOOPS`, so these tasks error
instead of being analyzed. An older build solved `while_infinite_loop_3` with the same
decomposition, so this may be a regression.
