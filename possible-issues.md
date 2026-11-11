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
