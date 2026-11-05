# Possible issues

Suspected bugs and smells found while working on the code, not yet addressed.

- The OC backend gives a wrong `true` for `valid-memsafety` when a thread returns a dead pointer and the joiner dereferences it: `void *w(void *a) { int *m = malloc(4); free(m); return m; }` with `pthread_join(t, &r); *(int *)r`, and likewise for a returned local. The model checks the object's size and the thread clears it before storing its result; the same dead pointer passed through a global is found.
- `ExprSimplifier.simplifyOr` returns true for a disjunction without operands, whereas evaluating `Or()` is false by definition. `MemsafetyPass.flatDerefCheck` guards against it.
- With a pointee type `MallocFunctionPass` cannot determine, the allocation bound stays in bytes under the cell models, which can miss an overrun.
- The Z3 user propagator crashes natively (`conflict_resolution::eq2literals`) if the first check after encoding is an OC exit query under a solver scope, e.g. on `pthread-complex/safestack_relacy` with `--oc-decision-procedure PROPAGATOR`. `XcfaOcChecker` avoids this by discharging dead targets only for the IDL procedure.
