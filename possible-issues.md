# Possible issues

Suspected bugs and smells found while working on the code, not yet addressed.

- `ExprSimplifier.simplifyOr` returns true for a disjunction without operands, whereas evaluating `Or()` is false by definition. `MemsafetyPass.flatDerefCheck` guards against it.
- The Z3 user propagator crashes natively (`conflict_resolution::eq2literals`) if the first check after encoding is an OC exit query under a solver scope, e.g. on `pthread-complex/safestack_relacy` with `--oc-decision-procedure PROPAGATOR`. `XcfaOcChecker` avoids this by discharging dead targets only for the IDL procedure.
