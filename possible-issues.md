# Possible issues

Suspected bugs and smells found while working on the code, not yet addressed.

- `ExprSimplifier.simplifyOr` returns true for a disjunction without operands, whereas evaluating `Or()` is false by definition. `MemsafetyPass.flatDerefCheck` guards against it.
- The address of a function's scalar local is not invalidated when the function returns: `int *f(void) { int x; return &x; }` followed by `*f() = 1` gives a wrong `true` for `valid-memsafety` on the default portfolio.
- With a pointee type `MallocFunctionPass` cannot determine, the allocation bound stays in bytes under the cell models, which can miss an overrun.
- The Z3 user propagator crashes natively (`conflict_resolution::eq2literals`) if the first check after encoding is an OC exit query under a solver scope, e.g. on `pthread-complex/safestack_relacy` with `--oc-decision-procedure PROPAGATOR`. `XcfaOcChecker` avoids this by discharging dead targets only for the IDL procedure.
