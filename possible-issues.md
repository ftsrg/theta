# Possible issues

Suspected bugs and smells found while working on something else. Delete an entry when it is fixed.

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
